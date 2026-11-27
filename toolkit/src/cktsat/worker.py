"""cktsat worker: one process, one core. Reads jobs (JSON lines) on stdin, answers on stdout.

    job:    {"id": 7, "lits": [..cube literals..], "budget": 200000}      budget <= 0: no limit
    answer: {"id": 7, "res": "UNSAT" | "SAT" | "UNK", "conf": n, "cpu": seconds, "model": [true vars] (SAT only)}

Solver modes (argv[2]):
    cadical195 | cadical300 | cadical153 | glucose42   one incremental solver, cubes are assumptions (learnt
                                                       clauses are kept from cube to cube)
    kissat | cadical195-fresh | cadical300-fresh       a fresh solver per cube, cube literals added as units
    auto                                               unit propagation, then fresh CaDiCaL for argv[4] conflicts,
                                                       then fresh Kissat for the cube's budget (all stateless, so
                                                       the answer for a cube does not depend on scheduling)
    cegar                                              incremental CaDiCaL on a growing subset of the points
                                                       (needs a CNF grouped by point and its .meta file)
"""
import json
import sys
import time


def read_dimacs(path):
    cls = []
    nv = 0
    with open(path) as f:
        for line in f:
            c = line[0]
            if c == 'c':
                continue
            if c == 'p':
                nv = int(line.split()[2])
                continue
            x = line.split()
            x.pop()
            cls.append([int(t) for t in x])
    return nv, cls


def read_dimacs_groups(path):
    """DIMACS written by `cktsat-core encode --cegar`: structural clauses, then 'c point p' blocks."""
    struct, blocks, cur = [], {}, None
    nv = 0
    with open(path) as f:
        for line in f:
            c = line[0]
            if c == 'c':
                if line.startswith('c point '):
                    cur = blocks.setdefault(int(line.split()[2]), [])
                continue
            if c == 'p':
                nv = int(line.split()[2])
                continue
            x = line.split()
            x.pop()
            (struct if cur is None else cur).append([int(t) for t in x])
    return nv, struct, blocks


def cegar_main(cnf_path, seed, q0):
    """Counterexample-guided worker: the solver only sees the clauses of a growing subset Q of the points. UNSAT on
    Q is UNSAT; a model is evaluated on all points and a wrong point is added to Q."""
    import random
    from pysat import solvers as S
    nv, struct, blocks = read_dimacs_groups(cnf_path)
    meta = json.load(open(cnf_path + '.meta'))
    N, P, K, s = meta['N'], meta['P'], meta['K'], meta['s']
    col = lambda t: int(t[::-1], 2)
    incols = [col(t) for t in meta['in']]
    tgt = [col(t) for t in meta['tgt']]
    care = [col(t) for t in meta['care']]
    full = (1 << P) - 1
    rng = random.Random(seed * 7919 + 13)
    Q = set(rng.sample(range(P), min(P, q0)))
    inc = S.Cadical195(bootstrap_with=struct)
    for p in sorted(Q):
        for c in blocks.get(p, []):
            inc.add_clause(c)

    def wrong_points(pos):
        w = list(incols)
        for i in range(s):
            s1b, s2b, t, ng = meta['gates'][i]
            nW = N + i
            b = next(k for k in range(nW) if (s2b + k) in pos)
            if ng in pos:
                w.append(full & ~w[b])
            else:
                a = next(j for j in range(nW) if (s1b + j) in pos)
                w.append((w[a] & w[b]) if t in pos else (w[a] | w[b]))
        bad = 0
        for k in range(K):
            o = N + s - 1 if K == 1 else next(x for x in range(N + s) if meta['osel'][k][x] and meta['osel'][k][x] in pos)
            bad |= (w[o] ^ tgt[k]) & care[k]
        return bad

    out = sys.stdout
    out.write(json.dumps({"ready": True, "vars": nv, "clauses": len(struct), "points": len(Q)}) + "\n")
    out.flush()
    last_conf = 0
    for line in sys.stdin:
        job = json.loads(line)
        if job.get("quit"):
            break
        lits, budget = job["lits"], job.get("budget", 0)
        t0 = time.process_time()
        remaining, conf, model = budget, 0, None
        while True:
            if budget > 0:
                inc.conf_budget(max(1, remaining))
                r = inc.solve_limited(assumptions=lits)
            else:
                r = inc.solve(assumptions=lits)
            c = inc.accum_stats().get('conflicts', 0)
            conf += c - last_conf
            remaining -= c - last_conf
            last_conf = c
            if not r:
                break
            m = inc.get_model()
            pos = set(x for x in m if x > 0)
            bad = wrong_points(pos)
            if bad == 0:
                model = m
                break
            lo = (bad & -bad).bit_length() - 1
            hi = bad.bit_length() - 1
            for p in {lo, hi}:
                if p not in Q:
                    Q.add(p)
                    for cl in blocks.get(p, []):
                        inc.add_clause(cl)
            if budget > 0 and remaining <= 0:
                r = None
                break
        ans = {"id": job["id"], "res": "UNK" if r is None else ("SAT" if r else "UNSAT"), "conf": conf,
               "cpu": round(time.process_time() - t0, 4), "stage": "cegar", "points": len(Q)}
        if r:
            ans["model"] = [x for x in model if x > 0]
        out.write(json.dumps(ans) + "\n")
        out.flush()


def main():
    cnf_path, mode, seed = sys.argv[1], sys.argv[2], int(sys.argv[3])
    pre_budget = int(sys.argv[4]) if len(sys.argv) > 4 else 2000
    if mode == 'cegar':
        return cegar_main(cnf_path, seed, int(sys.argv[5]) if len(sys.argv) > 5 else 16)
    from pysat import solvers as S
    nv, cls = read_dimacs(cnf_path)
    auto = mode == 'auto'
    fresh = auto or mode == 'kissat' or mode.endswith('-fresh')
    base = 'kissat' if auto else mode.replace('-fresh', '')
    klass = {'cadical195': S.Cadical195, 'cadical300': S.Cadical300, 'cadical153': S.Cadical153,
             'glucose42': S.Glucose42, 'kissat': S.Kissat404}[base]

    def configure(s, b):
        if b in ('cadical195', 'cadical300') and seed:
            try:
                s.configure({'seed': seed})
            except Exception:
                pass

    def conflicts(s):
        try:
            return s.accum_stats().get('conflicts', 0)
        except Exception:
            return 0

    def fresh_solve(kl, b, lits, budget):
        s = kl(bootstrap_with=cls)
        configure(s, b)
        for l in lits:
            s.add_clause([l])
        if budget > 0:
            s.conf_budget(budget)
            r = s.solve_limited()
        else:
            r = s.solve()
        model = s.get_model() if r else None
        c = conflicts(s)
        s.delete()
        return r, model, c

    inc = None
    up = None
    last_conf = 0
    if not fresh:
        inc = klass(bootstrap_with=cls)
        configure(inc, base)
    else:
        up = S.Cadical195(bootstrap_with=cls)     # only ever asked to unit-propagate: it never learns, so it is stateless
    out = sys.stdout
    out.write(json.dumps({"ready": True, "vars": nv, "clauses": len(cls)}) + "\n")
    out.flush()
    for line in sys.stdin:
        job = json.loads(line)
        if job.get("quit"):
            break
        lits, budget = job["lits"], job.get("budget", 0)
        t0 = time.process_time()
        stage = ''
        if fresh:
            r, model, conf = None, None, 0
            ok, _ = up.propagate(assumptions=lits)
            if not ok:
                r, stage = False, 'up'
            if r is None and auto:
                b0 = pre_budget if (budget <= 0 or budget > pre_budget) else budget
                r, model, conf = fresh_solve(S.Cadical195, 'cadical195', lits, b0)
                stage = 'pre'
            if r is None and not (auto and 0 < budget <= pre_budget):
                r, model, c2 = fresh_solve(klass, base, lits, budget)
                conf += c2
                stage = base
        else:
            if budget > 0 and base != 'cadical153':
                inc.conf_budget(budget)
                r = inc.solve_limited(assumptions=lits)
            else:
                r = inc.solve(assumptions=lits)
            model = inc.get_model() if r else None
            c = conflicts(inc)
            conf, last_conf = c - last_conf, c
            stage = base
        ans = {"id": job["id"], "res": "UNK" if r is None else ("SAT" if r else "UNSAT"), "conf": conf,
               "cpu": round(time.process_time() - t0, 4), "stage": stage}
        if r:
            ans["model"] = [x for x in model if x > 0]
        out.write(json.dumps(ans) + "\n")
        out.flush()


if __name__ == '__main__':
    main()
