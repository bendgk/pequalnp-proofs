#!/usr/bin/env python3
"""cktsat — exact circuit synthesis by SAT cube-and-conquer (multi-core).

    bin/cktsat SPEC --basis ao|aon|ao2 -s S [-j T]      circuit with exactly S gates, or UNSAT (exhaustive)
    bin/cktsat SPEC --basis B --min [--lb L] [--ub U]   minimum size: walks S = L, L+1, ... until SAT
    bin/cktsat SPEC --basis B -s S --upto               sizes L..S in turn (answers "at most S gates?")

Cubes are the canonical first-d-gate prefixes up to the symmetry group of the spec (computed natively by
bin/cktsat-core); a pool of exactly -j worker processes solves them; a cube that exceeds its conflict budget is
split one gate deeper. Every cube and its result goes to runs/cktsat_<spec>_<s>_<basis>.jsonl (journal, used by
--resume) and, when a size is finished, to the .json next to it. See docs/cktsat.md.
"""
import argparse
import collections
import json
import os
import random
import selectors
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
CORE = os.path.join(ROOT, 'bin', 'cktsat-core')
CHECK = os.path.join(ROOT, 'bin', 'cktcheck')
WORKER = os.path.join(HERE, 'worker.py')
CACHE_VERSION = 'cktsat-elim-3'      # bump whenever the encoder changes, so that old cofactor bounds are not reused


def log(*a):
    print(*a, file=sys.stderr, flush=True)


def core_args(cfg):
    a = [cfg.spec, '--basis', cfg.basis]
    if cfg.no_sym:
        a.append('--no-sym')
    if cfg.gcap:
        a += ['--gcap', str(cfg.gcap)]
    if cfg.no_mono_reduce:
        a.append('--no-mono-reduce')
    return a


def enc_args(cfg, s=None):
    a = ['--alldiff', str(cfg.alldiff), '--mono', str(cfg.mono), '--tri', str(cfg.tri), '--ess', str(cfg.ess),
         '--dep', str(cfg.dep), '--sens', str(cfg.sens)]
    eb = elim_E(cfg, s) if s is not None else []
    if eb:
        a += ['--elim-bounds', ','.join(f'{j}:{c}:{E}' for j, c, E in eb), '--elim-dead', str(cfg.elim_dead),
              '--elim-sem', str(cfg.elim_sem)]
    if cfg.cegar:
        a.append('--cegar')
    return a


def elim_E(cfg, s):
    """[(input, value, max number of gates that may vanish)] for size s, from the cofactor lower bounds."""
    return [(j, c, s - L) for (j, c, L) in getattr(cfg, 'cof_bounds', []) if s - L < s]


def cofactor_bounds(cfg, info):
    """Proven lower bounds L(f | x_j = c) for one input j per symmetry orbit, by running cktsat --min on the cofactor
    spec (recursively, cached in <logdir>/cktsat_elim/cache.json). Returns (per-input list [(j, c, L)], report)."""
    import hashlib
    edir = os.path.join(cfg.logdir if os.path.basename(cfg.logdir) != 'cktsat_elim' else os.path.dirname(cfg.logdir), 'cktsat_elim')
    os.makedirs(edir, exist_ok=True)
    cpath = os.path.join(edir, 'cache.json')
    try:
        cache = json.load(open(cpath))
    except Exception:
        cache = {}
    orbit = info['orbit']
    reps = sorted(set(o for o in orbit if o >= 0))
    per_rep, report = {}, []
    for j in reps:
        for c in (0, 1):
            tmp = os.path.join(edir, f'tmp_{os.getpid()}.spec')
            ci = json.loads(run_core(['cofactor'] + core_args(cfg) + ['--input', str(j), '--value', str(c), '-o', tmp])[0])
            text = open(tmp).read()
            key = hashlib.sha1((CACHE_VERSION + '\n' + cfg.basis + '\n' + text).encode()).hexdigest()[:16]
            cspec = os.path.join(edir, f'cof_{key}.spec')
            if ci['points'] == 0 or ci['inputs'] == 0:
                os.remove(tmp)
            else:
                os.replace(tmp, cspec)
            ent = cache.get(key)
            if ci['points'] == 0 or ci['inputs'] == 0:
                ent = dict(lb=0, exact=True, trivial=True)
            if ent is None or (not ent.get('exact') and ent.get('time_limit', 0) < cfg.elim_time):
                rj = os.path.join(edir, f'res_{key}_{os.getpid()}.json')
                a = [sys.executable, os.path.abspath(__file__), cspec, '--basis', cfg.basis, '--min', '--ub', str(cfg.elim_ub),
                     '-j', str(cfg.j), '--logdir', edir, '--result-json', rj, '--time-limit', str(cfg.elim_time), '--resume',
                     '--elim', 'auto' if cfg.elim_depth > 1 else 'off', '--elim-depth', str(cfg.elim_depth - 1),
                     '--elim-time', str(cfg.elim_time), '--solver', cfg.solver, '--budget', str(cfg.budget),
                     '--min-cubes', str(cfg.min_cubes), '--progress', str(cfg.progress), '--level', str(cfg.level + 1),
                     '--alldiff', str(cfg.alldiff), '--mono', str(cfg.mono), '--dep', str(cfg.dep), '--sens', str(cfg.sens),
                     '--pre-budget', str(cfg.pre_budget), '--growth', str(cfg.growth), '--cegar-points', str(cfg.cegar_points),
                     '--elim-dead', str(cfg.elim_dead), '--elim-sem', str(cfg.elim_sem)]
                if cfg.cegar:
                    a.append('--cegar')
                log(f'[cktsat]{"  " * cfg.level} elim: cofactor x{j}={c}: {ci["inputs"]} inputs, {ci["points"]} points -> {os.path.basename(cspec)}')
                child = subprocess.Popen(a, stdout=subprocess.DEVNULL)
                try:
                    child.wait()
                except BaseException:        # pass a termination on, so that the sub-run stops its workers
                    child.terminate()
                    try:
                        child.wait(timeout=15)
                    except Exception:
                        child.kill()
                    raise
                try:
                    res = json.load(open(rj))
                    os.remove(rj)
                except Exception:
                    res = dict(lb=0, exact=False)
                ent = dict(lb=res.get('lb', 0), exact=bool(res.get('exact')), trivial=bool(res.get('trivial')),
                           time_limit=cfg.elim_time, basis=cfg.basis, inputs=ci['inputs'], points=ci['points'],
                           const_output=bool(res.get('const_output')), rests_on=res.get('cofactors', []),
                           options=dict(elim_sem=cfg.elim_sem, elim_dead=cfg.elim_dead, cegar=cfg.cegar, solver=cfg.solver),
                           spec=os.path.basename(cspec), version=CACHE_VERSION)
                try:
                    cache = json.load(open(cpath))
                except Exception:
                    cache = {}
                cache[key] = ent
                with open(cpath + f'.{os.getpid()}', 'w') as f:
                    json.dump(cache, f, indent=1, sort_keys=True)
                os.replace(cpath + f'.{os.getpid()}', cpath)
            # a constant-true cofactor output costs one gate in the full model but none after simplification
            L = 0 if (ent.get('trivial') or ent.get('const_output')) else ent['lb']
            per_rep[(j, c)] = L
            report.append(dict(input=j, orbit_size=orbit.count(j), value=c, L=L, exact=bool(ent.get('exact')),
                               spec=os.path.relpath(cspec, ROOT), key=key))
    bounds = [(i, c, per_rep[(o, c)]) for i, o in enumerate(orbit) if o >= 0 for c in (0, 1) if per_rep[(o, c)] > 0]
    return bounds, report


def run_core(args, inp=None):
    r = subprocess.run([CORE] + args, input=inp, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit('cktsat: core failed: ' + ' '.join(args) + '\n' + r.stderr)
    return r.stdout, r.stderr


def parse_cubes(lines):
    out = []
    for l in lines:
        if not l.strip():
            continue
        p, lits = l.split('\t')
        out.append((p, [int(x) for x in lits.split()]))
    return out


class Splitter:
    """bin/cktsat-core serve: canonical one-gate extensions of a prefix."""

    def __init__(self, cfg, s):
        a = [CORE, 'serve'] + core_args(cfg) + ['-s', str(s)]
        if cfg.first:
            a += ['--first', cfg.first]
        self.p = subprocess.Popen(a, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)

    def split(self, prefix):
        self.p.stdin.write('split ' + prefix + '\n')
        self.p.stdin.flush()
        hdr = self.p.stdout.readline()
        if not hdr.startswith('n '):
            sys.exit('cktsat: core serve failed on prefix ' + prefix)
        lines = []
        while True:
            l = self.p.stdout.readline()
            if not l or l.strip() == 'end':
                break
            lines.append(l)
        return parse_cubes(lines)

    def close(self):
        try:
            self.p.stdin.write('quit\n')
            self.p.stdin.flush()
            self.p.wait(timeout=5)
        except Exception:
            self.p.kill()


class Worker:
    def __init__(self, cnf, mode, seed, idx, pre_budget=2000, q0=16):
        self.p = subprocess.Popen([sys.executable, WORKER, cnf, mode, str(seed + (idx if mode == 'cegar' else 0)),
                                   str(pre_budget), str(q0)], stdin=subprocess.PIPE,
                                  stdout=subprocess.PIPE, text=True, bufsize=1)
        self.job = None
        self.idx = idx
        self.ready = False

    def send(self, job):
        self.job = job
        self.p.stdin.write(json.dumps({"id": job['id'], "lits": job['lits'], "budget": job['budget']}) + '\n')
        self.p.stdin.flush()

    def kill(self):
        try:
            self.p.kill()
            self.p.wait(timeout=5)
        except Exception:
            pass


def names(cfg, s):
    spec = os.path.splitext(os.path.basename(cfg.spec))[0]
    tag = f'cktsat_{spec}_{s}_{cfg.basis}'
    if cfg.full_model:
        tag += '_full'
    if cfg.no_sym:
        tag += '_nosym'
    if cfg.first:
        tag += '_first-' + cfg.first.replace(' ', '-')
    if cfg.shard:
        tag += '_shard' + cfg.shard.replace('/', 'of')
    if cfg.tag:
        tag += '_' + cfg.tag
    d = cfg.logdir
    os.makedirs(d, exist_ok=True)
    return spec, os.path.join(d, tag + '.jsonl'), os.path.join(d, tag + '.json'), tag


def model_text(cfg):
    if cfg.full_model:
        return ('full model: every gate is AND/OR%s of <= 2 wires, constants, copies and missing-wire reads allowed '
                '(Lean semantics); satisfiable iff a circuit with AT MOST s gates exists' % ('/NOT' if cfg.basis == 'aon' else ''))
    return ('normal model: exactly s gates; AND/OR of two distinct earlier wires%s; every gate except an output is '
            'read; no gate column is constant or repeats an input/gate column on the points (%s); searched up to gate '
            'order (canonical (b,a,op) order) and up to the input symmetries of the spec (%s). Every minimum-size '
            'circuit of the full Lean model has this form, see docs/cktsat.md'
            % (', NOT of one earlier wire' if cfg.basis == 'aon' else '',
               'all cared points' if cfg.basis == 'aon' or cfg.no_mono_reduce else
               'the minimal true and maximal false cared points, which determine a monotone circuit',
               'not used' if cfg.no_sym else 'one canonical prefix per orbit'))


def solve_size(cfg, info, s):
    """Returns dict(result=SAT|UNSAT|UNKNOWN, ...)."""
    t_start = time.time()
    spec, jpath, fpath, tag = names(cfg, s)
    tmp = os.path.join(cfg.logdir, '.cktsat_tmp')
    os.makedirs(tmp, exist_ok=True)
    cnf = os.path.join(tmp, f'{tag}_{os.getpid()}.cnf')
    a = ['encode'] + core_args(cfg) + ['-s', str(s), '-o', cnf]
    a += ['--full-model'] if cfg.full_model else enc_args(cfg, s)
    encinfo = json.loads(run_core(a)[0])
    # root cubes
    if cfg.full_model:
        roots, depth0 = [('', [])], 0
    else:
        a = ['cubes'] + core_args(cfg) + ['-s', str(s), '-j', str(min(cfg.j, 3) if cfg.j > 1 else 1)]
        if cfg.depth is not None:
            a += ['--depth', str(cfg.depth)]
        else:
            a += ['--min-cubes', str(cfg.min_cubes)]
        if cfg.first:
            a += ['--first', cfg.first]
        out, _ = run_core(a)
        lines = out.splitlines()
        depth0 = int(lines[0].split()[1])
        roots = parse_cubes(lines[1:])
    nroots_all = len(roots)
    if cfg.shard:
        i, n = [int(x) for x in cfg.shard.split('/')]
        roots = [c for k, c in enumerate(roots) if k % n == i]
    hdr = dict(hdr=1, spec=os.path.basename(cfg.spec), basis=cfg.basis, s=s, model=model_text(cfg),
               N=info['N'], K=info['K'], points=info['P'], group=info['group'], group_truncated=info['group_truncated'],
               no_sym=cfg.no_sym, first=cfg.first, shard=cfg.shard, depth0=depth0, roots=len(roots), roots_all=nroots_all,
               enc=dict(alldiff=cfg.alldiff, mono=cfg.mono, tri=cfg.tri, ess=cfg.ess, dep=cfg.dep, sens=cfg.sens,
                        elim_sem=cfg.elim_sem, elim_dead=cfg.elim_dead, cegar=cfg.cegar, vars=encinfo['vars'],
                        clauses=encinfo['clauses']),
               elim=dict(mode=cfg.elim, max_vanishing=[list(x) for x in elim_E(cfg, s)],
                         cofactor_lower_bounds=getattr(cfg, 'cof_report', [])),
               solver='cegar/cadical195' if cfg.cegar and not cfg.full_model else cfg.solver, budget=cfg.budget, pre_budget=cfg.pre_budget, growth=cfg.growth, seed=cfg.seed)
    # journal / resume
    done = {}
    prev_cpu = 0.0
    if cfg.resume and os.path.exists(jpath):
        with open(jpath) as f:
            for line in f:
                try:
                    r = json.loads(line)
                except Exception:
                    continue
                if r.get('hdr') and r['hdr'] != 1:
                    continue                 # marker of an earlier --resume
                if r.get('hdr'):
                    for k in ('spec', 'basis', 's', 'no_sym', 'first', 'shard', 'depth0'):
                        if r.get(k) != hdr.get(k):
                            sys.exit(f'cktsat: --resume: journal {jpath} was made with different {k}')
                    old_e = sorted(map(tuple, (r.get('elim') or {}).get('max_vanishing', [])))
                    if old_e != sorted(map(tuple, hdr['elim']['max_vanishing'])):
                        sys.exit(f'cktsat: --resume: journal {jpath} was made with different elimination bounds '
                                 f'(journal: {old_e or "none"}); pass the same --elim')
                    hdr['elim'] = r.get('elim') or hdr['elim']
                else:
                    done[r['p']] = r
        jf = open(jpath, 'a')
        # the cubes below this line were solved with these (possibly different, always implied) clause options
        if not cfg.audit:
            jf.write(json.dumps(dict(hdr=2, resumed=time.strftime('%Y-%m-%d %H:%M:%S'), enc=hdr['enc'], solver=hdr['solver'],
                                 budget=cfg.budget, growth=cfg.growth)) + '\n')
    else:
        jf = open(jpath, 'w')
        jf.write(json.dumps(hdr) + '\n')
    jf.flush()
    splitter = None if cfg.full_model else Splitter(cfg, s)

    records = []     # (prefix, result, conflicts, cpu, children)
    queue = collections.deque()
    stats = dict(unsat=0, split=0, pruned=0, cpu=0.0, conf=0, maxdepth=depth0)

    def depth_of(prefix):
        return prefix.count(';') + 1 if prefix else 0

    def budget_for(depth):
        if cfg.full_model or cfg.budget <= 0 or depth >= s or depth >= cfg.max_split_depth:
            return 0
        return int(cfg.budget * (cfg.growth ** max(0, depth - depth0)))

    # rebuild the open frontier (also re-derives the whole cube tree of a finished journal: an audit of coverage)
    stack = list(reversed(roots))
    order = []
    uleaves = []
    while stack:
        p, lits = stack.pop()
        r = done.get(p)
        if r is None or r['r'] == 'S':
            order.append((p, lits))
        elif r['r'] == 'U':
            uleaves.append((p, lits))
            records.append((p, 'U', r.get('c', 0), r.get('t', 0.0), 0))
            stats['unsat'] += 1; stats['cpu'] += r.get('t', 0.0); stats['conf'] += max(0, r.get('c', 0))
            stats['maxdepth'] = max(stats['maxdepth'], depth_of(p))
        elif r['r'] == 'X':
            ch = splitter.split(p)
            records.append((p, 'X', r.get('c', 0), r.get('t', 0.0), len(ch)))
            stats['split'] += 1; stats['cpu'] += r.get('t', 0.0); stats['conf'] += max(0, r.get('c', 0))
            for c in reversed(ch):
                stack.append(c)
    if cfg.resume and done:
        log(f'[{tag}] resume: {stats["unsat"]} cubes already UNSAT, {stats["split"]} split, {len(order)} open')
        prev_cpu = stats['cpu']
    if cfg.seed:
        random.Random(cfg.seed).shuffle(order)
    if cfg.audit:
        jf.close()
        splitter.close() if splitter else None
        rechecked = 0
        if cfg.recheck and uleaves:
            # solve a random sample of the recorded UNSAT leaves again, with another solver, without a budget
            other = cfg.solver if cfg.solver != 'auto' else 'cadical195-fresh'
            sample = random.Random(cfg.seed + 1).sample(uleaves, min(cfg.recheck, len(uleaves)))
            w = Worker(cnf, other, cfg.seed, 0, cfg.pre_budget)
            try:
                assert json.loads(w.p.stdout.readline()).get('ready')
                for k, (p, lits) in enumerate(sample):
                    w.send(dict(id=k, p=p, lits=lits, budget=0))
                    ans = json.loads(w.p.stdout.readline())
                    if ans['res'] != 'UNSAT':
                        sys.exit(f'cktsat: AUDIT FAILED: cube "{p}" is recorded UNSAT but {other} says {ans["res"]}')
                    rechecked += 1
            finally:
                w.kill()
            log(f'[{tag}] audit: {rechecked} recorded UNSAT leaves solved again with {other}: all UNSAT')
        try:
            os.remove(cnf)
        except OSError:
            pass
        ok = not order
        return dict(result='UNSAT' if ok else 'UNKNOWN', s=s, log=fpath,
                    summary=dict(s=s, cubes=len(records), unsat=stats['unsat'], split=stats['split'], roots=len(roots),
                                 cpu=round(stats['cpu'], 2), wall=round(time.time() - t_start, 2), open=len(order),
                                 conflicts=stats['conf'], maxdepth=stats['maxdepth'], workers=0, audit=True,
                                 rechecked=rechecked,
                                 open_examples=[p for p, _ in order[:5]]))
    queue.extend(order)

    result = dict(result='UNKNOWN', s=s)
    nid = 0
    workers = []
    sel = selectors.DefaultSelector()
    try:
        if queue:
            nw = 1 if cfg.full_model else max(1, min(cfg.j, max(1, len(queue))))
            nw = cfg.j if not cfg.full_model else 1
            for i in range(nw):
                w = Worker(cnf, 'cegar' if cfg.cegar and not cfg.full_model else cfg.solver, cfg.seed, i,
                           cfg.pre_budget, cfg.cegar_points)
                workers.append(w)
                sel.register(w.p.stdout, selectors.EVENT_READ, w)
        idle = []
        busy = 0
        last = time.time()
        sat = None
        while (queue or busy) and sat is None:
            while idle and queue:
                w = idle.pop()
                p, lits = queue.popleft()
                d = depth_of(p)
                nid += 1
                w.send(dict(id=nid, p=p, lits=lits, budget=budget_for(d), depth=d))
                busy += 1
            for key, _ in sel.select(timeout=2.0):
                w = key.data
                line = w.p.stdout.readline()
                if not line:
                    sys.exit(f'cktsat: worker {w.idx} died')
                ans = json.loads(line)
                if ans.get('ready'):
                    w.ready = True
                    idle.append(w)
                    continue
                job = w.job
                w.job = None
                busy -= 1
                idle.append(w)
                p = job['p']
                stats['cpu'] += ans['cpu']; stats['conf'] += max(0, ans['conf'])
                stats['maxdepth'] = max(stats['maxdepth'], job['depth'])
                if ans['res'] == 'UNSAT':
                    stats['unsat'] += 1
                    records.append((p, 'U', ans['conf'], ans['cpu'], 0))
                    jf.write(json.dumps(dict(p=p, r='U', c=ans['conf'], t=ans['cpu'])) + '\n')
                elif ans['res'] == 'SAT':
                    records.append((p, 'S', ans['conf'], ans['cpu'], 0))
                    jf.write(json.dumps(dict(p=p, r='S', c=ans['conf'], t=ans['cpu'])) + '\n')
                    sat = (p, ans['model'])
                    break
                else:
                    ch = splitter.split(p)
                    stats['split'] += 1
                    records.append((p, 'X', ans['conf'], ans['cpu'], len(ch)))
                    jf.write(json.dumps(dict(p=p, r='X', c=ans['conf'], t=ans['cpu'], n=len(ch))) + '\n')
                    for c in reversed(ch):       # children first: keeps the frontier small
                        queue.appendleft(c)
            now = time.time()
            if now - last >= cfg.progress:
                last = now
                jf.flush()
                log(f'[{tag}] {now - t_start:7.1f}s  unsat={stats["unsat"]} split={stats["split"]} open={len(queue)} '
                    f'busy={busy} cpu={stats["cpu"]:.0f}s conf={stats["conf"]} maxdepth={stats["maxdepth"]}')
            if cfg.time_limit and now - t_start > cfg.time_limit and sat is None:
                log(f'[{tag}] time limit reached; journal kept for --resume')
                break
        jf.flush()
        wall = time.time() - t_start
        summary = dict(s=s, cubes=len(records), unsat=stats['unsat'], split=stats['split'], roots=len(roots),
                       cpu=round(stats['cpu'], 2), cpu_resumed=round(prev_cpu, 2), wall=round(wall, 2),
                       conflicts=stats['conf'], maxdepth=stats['maxdepth'], workers=cfg.j)
        if sat is not None:
            p, model = sat
            a = ['decode'] + core_args(cfg) + ['-s', str(s)] + (['--full-model'] if cfg.full_model else [])
            r = subprocess.run([CORE] + a, input=' '.join(map(str, model)), capture_output=True, text=True)
            if r.returncode != 0:
                sys.exit('cktsat: INTERNAL ERROR: SAT model does not verify\n' + r.stderr)
            summary['result'] = 'SAT'
            result = dict(result='SAT', s=s, ckt=r.stdout, cube=p, summary=summary)
        elif not queue and not busy:
            summary['result'] = 'UNSAT'
            result = dict(result='UNSAT', s=s, summary=summary)
        else:
            summary['result'] = 'UNKNOWN'
            summary['open'] = len(queue) + busy
            result = dict(result='UNKNOWN', s=s, summary=summary)
        hdr['summary'] = summary
        if summary['result'] != 'UNKNOWN':
            with open(fpath, 'w') as f:
                f.write('{"meta": ' + json.dumps(hdr) + ',\n "legend": "cubes: [prefix, U=UNSAT | X=split into its '
                        'canonical one-gate extensions | S=SAT, conflicts, cpu seconds, children]",\n "cubes": [\n')
                f.write(',\n'.join('  ' + json.dumps(list(r)) for r in records))
                f.write('\n]}\n')
            result['log'] = fpath
    finally:
        for w in workers:
            w.kill()
        if splitter:
            splitter.close()
        jf.close()
        for f in (cnf, cnf + '.meta'):
            try:
                os.remove(f)
            except OSError:
                pass
    return result


def write_found(cfg, s, ckt_text, note):
    spec = os.path.splitext(os.path.basename(cfg.spec))[0]
    if cfg.out:
        path = cfg.out
    elif os.path.dirname(os.path.abspath(cfg.spec)) == os.path.join(ROOT, 'specs'):
        found = os.environ.get('PNP_FOUND') or os.path.join(ROOT, 'found')
        os.makedirs(found, exist_ok=True)
        path = os.path.join(found, f'{spec}_{s}_{cfg.basis}.ckt')
        try:      # never overwrite a circuit that another tool put there
            if not open(path).readline().startswith('# cktsat'):
                path = os.path.join(found, f'{spec}_{s}_{cfg.basis}_cktsat.ckt')
        except OSError:
            pass
    else:
        os.makedirs(os.path.join(cfg.logdir, '.cktsat_tmp'), exist_ok=True)
        path = os.path.join(cfg.logdir, '.cktsat_tmp', f'{spec}_{s}_{cfg.basis}_{os.getpid()}.ckt')
    with open(path, 'w') as f:
        f.write(f'# cktsat: {note}\n' + ckt_text)
    r = subprocess.run([CHECK, cfg.spec, path, '--basis', cfg.basis, '--max', str(s)], capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f'cktsat: INTERNAL ERROR: bin/cktcheck rejects {path}\n{r.stdout}{r.stderr}')
    return path, r.stdout.strip()


def trivial(cfg, info):
    """K = 1 targets that need 0 or 1 gates. Returns (size, ckt text) or None."""
    t, N = info['trivial'], info['N']
    if t < 0:
        return None
    if t == 0:
        return 0, f'inputs {N}\nout {N}\n'                 # a missing wire reads false
    if t == 2:
        return 0, f'inputs {N}\nout {info["trivial_input"]}\n'
    if t == 3:
        return 1, f'inputs {N}\nnot {info["trivial_input"]}\nout {N}\n'
    if t == 1 and cfg.basis != 'ao2':
        return 1, f'inputs {N}\nand\nout {N}\n'            # 0-input AND = true
    return None


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('spec')
    ap.add_argument('--basis', default='ao', choices=['ao', 'aon', 'ao2'])
    ap.add_argument('-s', type=int, help='number of gates')
    ap.add_argument('--min', action='store_true', help='find the minimum size (walk up from --lb)')
    ap.add_argument('--upto', action='store_true', help='with -s: try sizes --lb..S in turn')
    ap.add_argument('--lb', type=int, default=1, help='smallest size to try (a lower bound you already trust)')
    ap.add_argument('--ub', type=int, default=64, help='--min: give up above this size')
    ap.add_argument('-j', type=int, default=int(os.environ.get('PNP_THREADS', '1')), help='worker processes')
    ap.add_argument('--seed', type=int, default=0, help='0 = canonical cube order; else shuffles cubes, seeds CaDiCaL')
    ap.add_argument('--solver', default='auto',
                    help='auto (unit propagation, CaDiCaL for --pre-budget conflicts, then Kissat; fresh solver per cube) | '
                         'kissat | cadical195-fresh | cadical300-fresh (fresh solver per cube) | '
                         'cadical195 | cadical300 | glucose42 (one incremental solver per worker, cubes as assumptions)')
    ap.add_argument('--pre-budget', type=int, default=2000, help='auto: conflicts of the cheap CaDiCaL pass')
    ap.add_argument('--depth', type=int, help='prefix length of the root cubes (default: until --min-cubes)')
    ap.add_argument('--min-cubes', type=int, default=200)
    ap.add_argument('--budget', type=int, default=200000, help='conflicts per cube before it is split (0 = never split)')
    ap.add_argument('--growth', type=float, default=1.5, help='budget multiplier per extra prefix gate')
    ap.add_argument('--max-split-depth', type=int, default=64)
    ap.add_argument('--first', help='fix gate 0, e.g. "and 0 1" (the search is then exhaustive for that choice only)')
    ap.add_argument('--shard', help='i/n: only root cubes with index = i mod n')
    ap.add_argument('--resume', action='store_true', help='continue from the journal of an earlier run')
    ap.add_argument('--audit', action='store_true',
                    help='solve nothing: recompute the cube tree of a finished journal and check that every leaf is recorded UNSAT')
    ap.add_argument('--full-model', action='store_true', help='Lean-exact degenerate gates, no symmetry, one SAT call')
    ap.add_argument('--recheck', type=int, default=0,
                    help='with --audit: solve this many randomly chosen recorded UNSAT leaves again (with --solver; '
                         'default CaDiCaL instead of Kissat)')
    ap.add_argument('--no-sym', action='store_true', help='do not use the symmetry group (validation)')
    ap.add_argument('--gcap', type=int, default=0, help='cap on the number of group elements used')
    ap.add_argument('--no-mono-reduce', action='store_true',
                    help='bases ao/ao2: keep all cared points instead of only minimal true / maximal false points')
    ap.add_argument('--alldiff', type=int, default=1)
    ap.add_argument('--mono', type=int, default=1)
    ap.add_argument('--tri', type=int, default=1)
    ap.add_argument('--ess', type=int, default=1)
    ap.add_argument('--dep', type=int, default=0, help='structural-support clauses (implied; off by default)')
    ap.add_argument('--sens', type=int, default=0,
                    help='1: reader-sensitivity clauses (implied): some reader of x_j differs on two points that '
                         'differ only in x_j and have different targets')
    ap.add_argument('--cegar', action='store_true',
                    help='counterexample-guided: workers run incremental CaDiCaL on a growing subset of the points '
                         '(for specs with many points, e.g. truth tables in basis aon)')
    ap.add_argument('--cegar-points', type=int, default=16, help='size of the initial point subset')
    ap.add_argument('--elim', default='off',
                    help='off | auto | "j:c:L,..." (j may be *). Elimination clauses: under x_j = c every gate reading '
                         'x_j vanishes, so at most s - L(f|x_j=c) gates read it. auto computes the cofactor lower '
                         'bounds L with cktsat itself (recursively); the UNSAT claim then rests on them')
    ap.add_argument('--elim-depth', type=int, default=3, help='recursion depth of --elim auto')
    ap.add_argument('--elim-sem', type=int, default=0,
                    help='1: the elimination count also includes gates whose column on the restricted points is constant or repeated')
    ap.add_argument('--elim-dead', type=int, default=0,
                    help='1: the elimination count also includes gates that are no longer needed after the restriction')
    ap.add_argument('--elim-time', type=float, default=300, help='seconds per size when bounding a cofactor')
    ap.add_argument('--elim-ub', type=int, default=40)
    ap.add_argument('--result-json', help='write a machine-readable summary here')
    ap.add_argument('--level', type=int, default=0, help=argparse.SUPPRESS)
    ap.add_argument('--out', help='where to write the circuit (default found/<spec>_<s>_<basis>.ckt for specs/ files)')
    ap.add_argument('--logdir', default=(os.environ.get('PNP_RUNS') or os.path.join(ROOT, 'runs')))
    ap.add_argument('--tag', default='')
    ap.add_argument('--time-limit', type=float, default=0, help='seconds per size; journal is kept for --resume')
    ap.add_argument('--progress', type=float, default=10.0)
    cfg = ap.parse_args()
    try:
        sys.stdout.reconfigure(line_buffering=True)
    except Exception:
        pass
    import signal

    def on_term(signum, frame):      # run the finally blocks: workers and sub-runs are stopped
        raise SystemExit(128 + signum)
    for sg in (signal.SIGTERM, signal.SIGHUP):
        signal.signal(sg, on_term)
    if not cfg.min and cfg.s is None:
        ap.error('give -s S or --min')
    if cfg.j < 1:
        cfg.j = 1
    if cfg.audit:
        cfg.resume = True
    t0 = time.time()
    info = json.loads(run_core(['prep'] + core_args(cfg))[0])
    spec = os.path.splitext(os.path.basename(cfg.spec))[0]
    log(f'[cktsat] {spec}: inputs={info["N"]} outputs={info["K"]} points={info["P"]} (of {info["P_orig"]}) '
        f'symmetry group order={info["group"]}{" (truncated)" if info["group_truncated"] else ""} basis={cfg.basis} '
        f'workers={cfg.j} solver={cfg.solver}')
    def result_json(d):
        if cfg.result_json:
            with open(cfg.result_json, 'w') as f:
                json.dump(d, f)

    tr = trivial(cfg, info)
    if info['size0']:
        tr = (0, f'inputs {info["N"]}\nout ' + ' '.join(map(str, info['size0'])) + '\n')
    if tr is not None and (tr[0] == 0 or not cfg.full_model):
        size, text = tr
        path, chk = write_found(cfg, size, text, 'trivial target')
        print(f'SAT {spec} basis={cfg.basis} size={size} (trivial target; this is the minimum)  file={path}')
        print(chk)
        print(text, end='')
        result_json(dict(min=size, lb=size, exact=True, trivial=True))
        return 0
    if info['const_output'] and not cfg.full_model:
        result_json(dict(min=None, lb=0, exact=False, const_output=True))
    if info['trivial'] == 1 and cfg.basis == 'ao2' and not cfg.full_model:
        sys.exit('cktsat: target is constant true and basis ao2 has no constants: use --full-model')
    cfg.cof_bounds, cfg.cof_report = [], []
    if cfg.elim != 'off' and not cfg.full_model:
        if cfg.elim == 'auto':
            cfg.cof_bounds, cfg.cof_report = cofactor_bounds(cfg, info)
        else:
            for part in cfg.elim.split(','):
                j, c, L = part.split(':')
                for i, o in enumerate(info['orbit']):
                    if o >= 0 and (j == '*' or int(j) == i):
                        cfg.cof_bounds.append((i, int(c), int(L)))
                cfg.cof_report.append(dict(input=j, value=int(c), L=int(L), exact=None, spec='(given on the command line)'))
        for r in cfg.cof_report:
            msg = (f'elim: input {r["input"]}' + (f' (orbit of {r["orbit_size"]})' if 'orbit_size' in r else '')
                   + f' = {r["value"]}: cofactor needs >= {r["L"]} gates'
                   + ('' if r['exact'] is None else (' (exact)' if r['exact'] else ' (lower bound only)')) + f'  [{r["spec"]}]')
            log(f'[cktsat]{"  " * cfg.level} ' + msg)
            if cfg.level == 0:
                print(msg)
    if cfg.min:
        sizes = list(range(max(1, cfg.lb), cfg.ub + 1))
    elif cfg.upto:
        sizes = list(range(max(1, cfg.lb), cfg.s + 1))
    else:
        sizes = [cfg.s]
    proved = []
    rc = 1
    final = dict(min=None, lb=sizes[0] if (cfg.min or cfg.upto) and cfg.lb <= 1 else 0, exact=False, cofactors=cfg.cof_report)
    for s in sizes:
        if any(E < 0 for (_, _, E) in elim_E(cfg, s)):
            proved.append(s)       # a cofactor alone needs more than s gates
            if final['lb'] == s:
                final['lb'] = s + 1
            print(f'UNSAT {spec} basis={cfg.basis} s={s}  (a cofactor lower bound exceeds s)')
            rc = 20
            continue
        r = solve_size(cfg, info, s)
        sm = r['summary']
        if r['result'] == 'SAT':
            note = f'{spec} basis {cfg.basis} size {s}, cube "{r["cube"]}", wall {sm["wall"]}s cpu {sm["cpu"]}s -j {cfg.j}'
            path, chk = write_found(cfg, s, r['ckt'], note)
            print(f'SAT {spec} basis={cfg.basis} s={s}  cubes={sm["cubes"]} cpu={sm["cpu"]}s wall={sm["wall"]}s -j {cfg.j}  file={path}')
            print(chk)
            print(r['ckt'], end='')
            if proved and proved == list(range(proved[0], s)):
                lo = proved[0]
                what = 'at most' if cfg.full_model else 'exactly'
                print(f'MINIMUM {spec} basis={cfg.basis}: {s}  (UNSAT proved for {what} s={lo}..{s - 1}'
                      + ('' if lo <= 1 else f'; sizes below {lo} rest on your --lb') + ')')
            rc = 0
            if final['lb'] == s:
                final.update(min=s, exact=True)
            else:
                final.update(min=s)
            break
        elif r['result'] == 'UNSAT' and cfg.audit:
            sc = (f' shard {cfg.shard}' if cfg.shard else '') + (f' first="{cfg.first}"' if cfg.first else '')
            print(f'AUDIT OK {spec} basis={cfg.basis} s={s}{sc}: the journal covers all {sm["roots"]} root cubes{" of this shard" if cfg.shard else ""}; '
                  f'{sm["unsat"]} leaves recorded UNSAT, {sm["split"]} splits recomputed, 0 open  (recorded cpu {sm["cpu"]}s)'
                  + (f'; {sm["rechecked"]} leaves solved again with another solver: all UNSAT' if sm.get('rechecked') else ''))
            rc = 20
        elif cfg.audit:
            print(f'AUDIT FAILED {spec} basis={cfg.basis} s={s}: {sm["open"]} cubes are not covered, e.g. {sm["open_examples"]}')
            rc = 3
            break
        elif r['result'] == 'UNSAT':
            proved.append(s)
            if final['lb'] == s:
                final['lb'] = s + 1
            scope = ''
            if cfg.first:
                scope += f' [ONLY circuits whose first canonical gate is "{cfg.first}"]'
            if cfg.shard:
                scope += f' [ONLY shard {cfg.shard} of the root cubes]'
            print(f'UNSAT {spec} basis={cfg.basis} s={s}{scope}  cubes={sm["cubes"]} (leaves {sm["unsat"]}, split {sm["split"]}, '
                  f'roots {sm["roots"]}) cpu={sm["cpu"]}s wall={sm["wall"]}s -j {cfg.j}  log={r["log"]}')
            rc = 20
        else:
            print(f'UNKNOWN {spec} basis={cfg.basis} s={s}: stopped with {sm.get("open", "?")} cubes open '
                  f'(done {sm["unsat"]} UNSAT, {sm["split"]} split) cpu={sm["cpu"]}s wall={sm["wall"]}s; use --resume')
            rc = 3
            break
    if proved:
        print('  UNSAT covers the ' + model_text(cfg))
        if cfg.cof_bounds:
            print('  and it RESTS ON the cofactor lower bounds listed above (elimination clauses)')
    result_json(final)
    log(f'[cktsat] total wall {time.time() - t0:.1f}s')
    return rc


if __name__ == '__main__':
    sys.exit(main())
