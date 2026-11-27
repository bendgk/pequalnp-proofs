"""kn_cubes.py — cube-and-conquer driver for kn_elim.py (K(n) exact search).

    satpy kn_cubes.py N S --elim E [--depth D] [-j T] [--solver kissat404] [--distinct] [--inc]
                          [--log runs/knN_S.jsonl] [--resume] [--out found/knN_S_ao.ckt] [--no-sym]

Cube domain: every assignment of (first operand a, second operand b, type) to gates 0..D-1, a < b < wires available.
The domain is enumerated level by level; a prefix is dropped when
  (up)  unit propagation on the FULL CNF refutes it (then every extension is refuted too), or
  (sym) it is not the lex-min member of its isomorphism class under input relabelings and reorderings of the
        prefix gates.  Sound because the CNF's symmetry clauses (G, F, tie-break) are exactly necessary conditions of
        "the circuit is the lex-min member of its orbit" (key sequence ((b,a,type))_gates, OR < AND): the lex-min
        member's D-gate prefix is itself lex-min in its prefix class, otherwise transforming the whole circuit would
        give a smaller member.  So a solution exists iff one exists whose prefix survives (sym).
The surviving cubes go to a bounded pool of exactly T worker processes.  Default: a fresh solver per cube with the
cube as unit clauses; --inc: one incremental solver per worker with assumptions.
Every cube and its result is appended to the log; --resume skips cubes already logged UNSAT.
"""
import itertools, json, multiprocessing as mp, os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kn_elim


def gate_domain(n, i):
    W = n + i
    return [(a, b, t) for b in range(1, W) for a in range(b) for t in (0, 1)]


def lits(E, cube):
    out = []
    for i, (a, b, t) in enumerate(cube):
        out += [E['a'][i][a], E['b'][i][b], E['t'][i] if t else -E['t'][i]]
    return out


def canon(n, cube):
    """lex-min key sequence ((b,a,t),...) over prefix-gate reorderings x input relabelings."""
    D = len(cube)
    best = [None]

    def rec(order, placed, lab, nxt, keys):
        # order: list of original gate indices placed so far; lab: original input -> new label
        if best[0] is not None and keys > best[0][:len(keys)]:
            return
        if len(order) == D:
            if best[0] is None or keys < best[0]: best[0] = list(keys)
            return
        for g in range(D):
            if g in placed: continue
            a, b, t = cube[g]
            ops = (a, b)
            if any(o >= n and (o - n) not in placed for o in ops): continue      # must come after gates it reads
            new_inputs = [o for o in ops if o < n and o not in lab]
            choices = [new_inputs] if len(new_inputs) < 2 else [new_inputs, new_inputs[::-1]]
            for ch in choices:
                lab2 = dict(lab)
                for k, o in enumerate(ch): lab2[o] = nxt + k
                idx = []
                for o in ops:
                    idx.append(lab2[o] if o < n else n + order.index(o - n))
                key = (max(idx), min(idx), t)
                rec(order + [g], placed | {g}, lab2, nxt + len(ch), keys + [key])
    rec([], frozenset(), {}, 0, [])
    return best[0]


def is_canonical(n, cube):
    return [(b, a, t) for (a, b, t) in cube] == canon(n, cube)


def worker(n, s, elim, distinct, solver, inc, q, rq, extra=False):
    from pysat.solvers import Solver
    E = kn_elim.build(n, s, elim=elim, distinct=distinct, extra=extra)
    S = Solver(name=solver, bootstrap_with=E['cl']) if inc else None
    while True:
        item = q.get()
        if item is None: break
        idx, cube = item
        t0 = time.time()
        if inc:
            ok = S.solve(assumptions=lits(E, cube)); model = S.get_model() if ok else None
        else:
            S1 = Solver(name=solver, bootstrap_with=E['cl'] + [[l] for l in lits(E, cube)])
            ok = S1.solve(); model = S1.get_model() if ok else None
            S1.delete()
        res = dict(idx=idx, cube=cube, res='SAT' if ok else 'UNSAT', t=round(time.time() - t0, 2))
        if ok:
            g = kn_elim.decode(E, model, n, s)
            res['gates'] = g
            res['ok'] = kn_elim.check(g, n)
        rq.put(res)


def main():
    A = sys.argv[1:]
    n, s = int(A[0]), int(A[1])
    o = dict(elim=None, depth=3, j=int(os.environ.get('PNP_THREADS', '1')), log=None, out=None, solver='kissat404',
             distinct=False, resume=False, inc=False, sym=True, extra=False)
    i = 2
    while i < len(A):
        k = A[i]
        if k == '--elim': o['elim'] = int(A[i + 1]); i += 2
        elif k == '--depth': o['depth'] = int(A[i + 1]); i += 2
        elif k == '-j': o['j'] = int(A[i + 1]); i += 2
        elif k == '--log': o['log'] = A[i + 1]; i += 2
        elif k == '--out': o['out'] = A[i + 1]; i += 2
        elif k == '--solver': o['solver'] = A[i + 1]; i += 2
        elif k == '--distinct': o['distinct'] = True; i += 1
        elif k == '--resume': o['resume'] = True; i += 1
        elif k == '--inc': o['inc'] = True; i += 1
        elif k == '--no-sym': o['sym'] = False; i += 1
        elif k == '--extra': o['extra'] = True; i += 1
        else: sys.exit(__doc__)
    from pysat.solvers import Glucose4
    E = kn_elim.build(n, s, elim=o['elim'], distinct=o['distinct'], extra=o['extra'])
    up = Glucose4(bootstrap_with=E['cl'])
    t0 = time.time()
    level = [()]
    domain = 1; n_up = n_sym = 0
    for d in range(o['depth']):
        dom = gate_domain(n, d)
        domain *= len(dom)
        nxt = []
        tail = 1
        for d2 in range(d + 1, o['depth']): tail *= len(gate_domain(n, d2))     # extensions each dropped prefix stands for
        for pre in level:
            for g in dom:
                cube = pre + (g,)
                okp, _ = up.propagate(assumptions=lits(E, cube))
                if not okp: n_up += tail; continue
                if o['sym'] and not is_canonical(n, cube): n_sym += tail; continue
                nxt.append(cube)
        level = nxt
    up.delete()
    live_all = level
    done = set()
    if o['resume'] and o['log'] and os.path.exists(o['log']):
        for line in open(o['log']):
            try: d = json.loads(line)
            except Exception: continue
            if d.get('res') == 'UNSAT': done.add(tuple(map(tuple, d['cube'])))
    live = [c for c in live_all if c not in done]
    logf = open(o['log'], 'a') if o['log'] else None
    hdr = dict(kind='header', n=n, s=s, elim=o['elim'], depth=o['depth'], distinct=o['distinct'], solver=o['solver'],
               inc=o['inc'], sym=o['sym'], extra=o['extra'], domain=domain, refuted_by_unit_propagation=n_up, dropped_non_canonical=n_sym,
               to_solve=len(live_all), already_unsat_in_log=len(live_all) - len(live), vars=E['nv'], clauses=len(E['cl']),
               enum_seconds=round(time.time() - t0, 1))
    assert n_up + n_sym + len(live_all) == domain
    print(json.dumps(hdr), flush=True)
    if logf: logf.write(json.dumps(hdr) + '\n'); logf.flush()
    q, rq = mp.Queue(), mp.Queue()
    for idx, cube in enumerate(live): q.put((idx, cube))
    T = max(1, o['j'])
    for _ in range(T): q.put(None)
    ws = [mp.Process(target=worker, args=(n, s, o['elim'], o['distinct'], o['solver'], o['inc'], q, rq, o['extra']), daemon=True)
          for _ in range(T)]
    for w in ws: w.start()
    n_unsat = 0; cpu = 0.0; sat = None; last = time.time()
    for k in range(len(live)):
        r = rq.get()
        cpu += r['t']
        if logf: logf.write(json.dumps(r) + '\n'); logf.flush()
        if r['res'] == 'SAT':
            sat = r; break
        n_unsat += 1
        if time.time() - last > 60:
            last = time.time()
            print(f"  [{time.time() - t0:7.0f}s] {n_unsat}/{len(live)} cubes UNSAT, cpu {cpu:.0f}s, last {r['t']}s {r['cube']}", file=sys.stderr, flush=True)
    wall = time.time() - t0
    if sat:
        for w in ws: w.terminate()
        g = sat['gates']
        txt = f"inputs {n}\n" + ''.join(f"{op} {j} {k}\n" for op, j, k in g) + f"out {n + s - 1}\n"
        print(f"RESULT kn{n} s={s}: SAT (verified={sat['ok']}) wall {wall:.1f}s cpu {cpu:.1f}s")
        print(txt, end='')
        if o['out']: open(o['out'], 'w').write(txt)
    else:
        for w in ws: w.join()
        print(f"RESULT kn{n} s={s} elim={o['elim']}: UNSAT — domain {domain} cubes: {n_up} refuted by unit propagation, "
              f"{n_sym} non-canonical (symmetric to a kept cube), {len(live_all) - len(live)} UNSAT in an earlier log, "
              f"{n_unsat} UNSAT by CDCL now; wall {wall:.1f}s cpu {cpu:.1f}s, -j {T}, solver {o['solver']}")
    if logf:
        logf.write(json.dumps(dict(kind='summary', result='SAT' if sat else 'UNSAT', wall=round(wall, 1), cpu=round(cpu, 1))) + '\n')


if __name__ == '__main__':
    main()
