#!/usr/bin/env python3
"""leancheck -- lint a proof file by the pequalnp.com rules, then build it in the local sandbox.

  leancheck OUT.lean [--statement-file STMT.txt] [--allow-import MODULE]... [--lint-only]
            [--numerals strict|warn] [--real] [--in-slot] [-c CORES] [-m GB] [-t SECONDS] [--keep-name] [--keep-file]

Lint (mirrors tools/pnp.sh `check` and .github/scripts/outside-guard.mjs of pequalnp-proofs, plus join.txt):
  size 1..524288 bytes, UTF-8, no NUL/control/invisible characters; import lines first, only Mathlib[.x] or a
  module named with --allow-import (default: PEqualNP.Defs); the plain-file word list (double quote, # commands,
  set_option other than the four limits written `set_option <limit> <n> in`, attributes other than @[simp] and
  @[local simp], native, sorry, macro, syntax, notation, elab, ...), searched in code AND comments; at least one
  theorem; the own-namespace rule (helpers inside `namespace PEqualNP.Outside.<M>[_aux]`, the theorem last at top
  level with its full name); numerals: any run of 21 or more digit characters, and any numeral of more than 20
  hex digits, is an ERROR outside the theorem statement and a WARNING inside it (the statement is the desk's text).
  This is the strict reading; files already on main (L_meta_19034, L_meta_19358) do carry such numerals inside
  definitions and lists, so `--numerals warn` only warns (use it to time somebody else's accepted file).
  With --statement-file: the theorem must carry that text verbatim.
Build: the file is copied to $PNP_LEAN_SANDBOX (default toolkit/.cache/proofs-sandbox)/lean/PEqualNP/Outside/<M>.lean and built with
  bin/pnprun -c 2 -m 10 -t 2400 -- lake build PEqualNP.Outside.<M>     (one build at a time; never the network;
  the run is killed if lake starts to fetch or to compile Mathlib). If <M> is already on main in pequalnp-proofs
  the copy is renamed <M>_lc (text substitution) unless --keep-name. The copy is removed from the sandbox when
  leancheck ends, unless --keep-file. After a good build the axioms the theorem
  rests on are printed by a separate throwaway file and must be within propext, Classical.choice, Quot.sound.
--in-slot: leancheck is itself running under bin/pnprun (one slot for the build, the axioms and --real together):
  bin/pnprun -c 1 -m 10 -t 2400 -- bin/leancheck --in-slot OUT.lean ...   No inner pnprun is started.
--real (needs --statement-file): after a good build also run the project's own checker from the sandbox copy,
  `node tools/check-lean.mjs <file> <statement> check` (builds its verifier once, re-checks every declaration in the
  kernel on top of all of Mathlib, compares the statement term). Local only: its queue directory is toolkit/.cache/pequalnp-home.
Prints: LINT ok|FAIL, BUILD ok|FAIL, seconds (wall, lake's own real time, cpu), peak resident memory of the largest
process (from /usr/bin/time -l; it shrinks when the machine is short of memory, because mapped .olean pages are
evicted), peak footprint of the lean process (anonymous memory, sampled twice a second; the steadier number), and
PASS or FAIL.
Exit status 0 = PASS, 1 = FAIL, 2 = usage, 3 = could not judge (sandbox missing, lake wanted the network, ...).
"""
import fcntl, os, re, shutil, subprocess, sys, time, unicodedata

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
# The toolkit lives at <repo>/toolkit, so the Lean repo is the parent of ROOT (override: PNP_LEAN_REPO).
# Builds happen in a separate clone of that repo (override: PNP_LEAN_SANDBOX) so the working tree stays clean.
MAIN_REPO = os.environ.get('PNP_LEAN_REPO') or os.path.dirname(ROOT)
SANDBOX = os.environ.get('PNP_LEAN_SANDBOX') or os.path.join(ROOT, '.cache', 'proofs-sandbox')
MAX_BYTES = 512 * 1024

WS = "\t\n\v\f\r                  　﻿"
S = "[" + WS + "]"
B, A = r"(?<![A-Za-z0-9_])", r"(?![A-Za-z0-9_])"
LIM = r"set_option (maxRecDepth|maxHeartbeats|synthInstance\.maxSize|synthInstance\.maxHeartbeats) [0-9]+"
DQ = chr(34)
FORB = re.compile(DQ + r"|[«»]|simproc|builtin_|native|bv_decide|ofReduce|reduceNat|reduceBool|" + B + "(Lean|System|IO|Elab|Meta|Lake|FS|Process|EIO)" + A
                  + r"|_root_|RealWorld|BaseIO|include_str|notation|[A-Za-z_][A-Za-z0-9_']*[A-Za-z0-9_']%|polyrith|initialize|run_cmd|run_tac|run_elab|run_meta|by_elab|" + B + "elab|" + B + "macro|" + B + "syntax" + A
                  + "|" + B + "attribute" + A + "|" + B + "axiom" + A + "|" + B + "opaque" + A + "|unsafe|" + B + "partial" + A + "|sorry|" + B + "admit" + A + r"|#[a-z_][a-z_]{2,}|implemented_by|extern|`\([a-z]+\||\$\(|%\[|@\["
                  + "|register_|declare_|lcProof|lcUnreachable|" + B + "infix|" + B + "prefix" + A + "|" + B + "postfix" + A + "|set_option|binder_predicate|unif_hint|^" + S + r"*add_[A-Za-z0-9_]+|unseal|compile_inductive|irreducible_def|proof_wanted|mk_iff_of_inductive_prop")


def uni(s):
    return "".join(c if c < "\x80" else "a" if unicodedata.category(c)[0] == "L" else "0" if unicodedata.category(c)[0] == "N" else c for c in s)


def blank_comments(text):
    out = []
    i = 0
    depth = 0
    n = len(text)
    while i < n:
        if depth > 0:
            if text.startswith('/-', i):
                depth += 1; out.append('  '); i += 2
            elif text.startswith('-/', i):
                depth -= 1; out.append('  '); i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif text.startswith('/-', i):
            depth = 1; out.append('  '); i += 2
        elif text.startswith('--', i):
            j = text.find('\n', i)
            e = n if j < 0 else j
            out.append(' ' * (e - i)); i = e
        else:
            out.append(text[i]); i += 1
    return ''.join(out)


def lint(raw, mod, allowed, statement=None, numerals='strict'):
    """returns (errors, warnings)"""
    E, W = [], []
    if not (1 <= len(raw) <= MAX_BYTES):
        E.append('the file is %d bytes; a proof file must be 1 to %d bytes' % (len(raw), MAX_BYTES))
    try:
        t = raw.decode('utf-8')
    except UnicodeDecodeError:
        return E + ['the file is not UTF-8 text'], W
    if t.startswith('﻿'):
        t = t[1:]
    if '\0' in t:
        return E + ['the file holds a NUL byte'], W
    if re.search('[\x00-\x08\x0b-\x1f\x7f]', re.sub(r'\r?\n', '', t)):
        return E + ['the file holds control characters'], W
    if re.search('[​-‏‪-‮⁠-⁩﻿]', t):
        return E + ['the file holds invisible or direction-changing characters'], W
    if not re.fullmatch(r'L_[a-z0-9_]+', mod):
        E.append('the file must be lean/PEqualNP/Outside/L_<gap>.lean (lower case letters, digits, underscores); got %s' % mod)
    if mod.endswith('_aux'):
        E.append('the file name may not end in _aux')
    full = 'PEqualNP.Outside.' + mod
    L = [l[:-1] if l.endswith('\r') else l for l in t.split('\n')]
    # imports
    i = 0
    while i < len(L) and (not L[i].strip(WS) or re.fullmatch(r'import ([A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)*)[ \t]*', L[i])):
        n = L[i].strip(WS) and L[i].split(' ')[1].rstrip(' \t')
        if n and not (n == 'Mathlib' or n.startswith('Mathlib.') or n in allowed):
            E.append('line %d: import %s is not allowed (only Mathlib and the modules the gap lists; pass --allow-import %s if the gap lists it)' % (i + 1, n, n))
        i += 1
    for k in range(i, len(L)):
        if re.search(r'(^|[^A-Za-z0-9_])import([^A-Za-z0-9_]|$)', L[k]):
            E.append('line %d: the word import after the import lines' % (k + 1))
    # plain-file word list, comments included
    th = 0
    for k, l in enumerate(L):
        m = FORB.search(re.sub(r'@\[(local )?simp\]', '', re.sub(LIM + ' in' + A, '', l)))
        if m:
            E.append('line %d: %r is not allowed in a proof file, in code or in a comment' % (k + 1, m.group(0).strip(WS)))
        th += bool(re.match(S + r'*(@\[(local )?simp\] )?((private|protected) )?theorem ', l))
    if not th:
        E.append('the file holds no theorem')
    # own-namespace rule
    ID = r"[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*"
    Wd = lambda ws: re.compile(r"(?<![A-Za-z0-9_.'!?])(?:" + ws + r")(?![A-Za-z0-9_'!?])")
    SW = Wd('namespace|section|end|mutual')
    AT = Wd('def|theorem|lemma|abbrev|instance|structure|class|inductive|coinductive|example|opaque|axiom|noncomputable|private|protected|partial|unsafe|variable|universe|attribute|export|deriving|alias|local|scoped|omit|include|mk_iff_of_inductive_prop')
    own = lambda n: n == full or n.startswith(full + '.') or n == full + '_aux' or n.startswith(full + '_aux.')
    stack = []
    thm = False
    thm_line = None
    for k, l in enumerate(blank_comments(t).split('\n')):
        l = l[:-1] if l.endswith('\r') else l
        code = l.rstrip(' \t')
        c2 = uni(code)
        at = 'line %d' % (k + 1)
        if not code.strip(WS):
            continue
        if SW.search(c2):
            m = re.fullmatch('(?:(namespace) (' + ID + ')|(noncomputable section|section)(?: (' + ID + '))?|(end)(?: (' + ID + '))?|(mutual))[ \t]*', c2)
            g = lambda j: m.group(j) and code[m.start(j):m.end(j)]
            if not m:
                E.append(at + ': namespace, section, end and mutual must stand alone at the start of a line')
            elif thm:
                E.append(at + ': nothing but the proof may follow the theorem')
            elif m.group(1):
                if not stack and not own(g(2)):
                    E.append(at + ': namespace %s at the top level; the only namespace allowed there is the file\'s own' % g(2))
                stack.append(('namespace', g(2)))
            elif m.group(3) or m.group(7):
                if not stack:
                    E.append(at + ': a section or mutual at the top level')
                stack.append(('section', g(4)) if m.group(3) else ('mutual', None))
            else:
                top = stack.pop() if stack else None
                if not top:
                    E.append(at + ': end with nothing open to close')
                elif (g(6) is not None) if top[0] == 'mutual' else g(6) != top[1]:
                    E.append(at + ': end does not name what it closes')
        elif thm:
            w = AT.search(c2)
            if w:
                E.append(at + ': %r after the theorem; nothing but its proof may follow it' % w.group(0))
        elif stack or re.fullmatch(r'import [^ \t]+', code) or re.fullmatch(LIM + r' in[ \t]*', code):
            pass
        elif re.match(r'open[ \t]', code):
            if re.search(r'[ \t]in[ \t]+[^' + WS + ']', code):
                E.append(at + ': an open ... in line must end with in, with the theorem on the next line')
        elif re.match('theorem ' + re.escape(full) + r"(?![A-Za-z0-9_'!?.])", c2):
            thm = True
            thm_line = k
        else:
            E.append(at + ': a declaration or command outside the file\'s own namespace')
    if not thm:
        E.append('the theorem must stand at the top level, last, written with its full name: theorem %s ...' % full)
    # numerals (join.txt: a numeral longer than 20 digits is refused)
    span = (len(t), len(t))
    if thm_line is not None:
        start = sum(len(x) + 1 for x in t.split('\n')[:thm_line])
        depth = 0
        end = len(t)
        j = start
        while j < len(t):
            c = t[j]
            if c in '([{⟨':
                depth += 1
            elif c in ')]}⟩':
                depth -= 1
            elif depth == 0 and t.startswith(':=', j):
                end = j
                break
            j += 1
        span = (start, end)
        if statement is not None:
            norm = lambda s: re.sub(r'\s+', ' ', s).strip()
            head = 'theorem ' + full + ' :'
            got = norm(t[start:end])
            want = norm(statement)
            if not (got.startswith(head) and (norm(got[len(head):]) == want or norm(got[len(head):]) == '(' + want + ')')):
                E.append('the theorem does not carry the statement of the statement file verbatim')
    seen = set()
    for m in re.finditer(r'0[xX][0-9a-fA-F]{21,}|[0-9]{21,}', t):
        inside = span[0] <= m.start() < span[1]
        ln = t.count('\n', 0, m.start()) + 1
        kind = 'a numeral of %d hex digits' % (len(m.group(0)) - 2) if m.group(0)[:2] in ('0x', '0X') else 'a run of %d digit characters' % len(m.group(0))
        if inside or numerals == 'warn':
            if not inside:
                if 'out' not in seen:
                    seen.add('out')
                    W.append('line %d: %s outside the theorem statement (and maybe more); --numerals warn was given, so not counted' % (ln, kind))
            elif 'stmt' not in seen:
                seen.add('stmt')
                W.append('line %d: the theorem statement holds %s (and maybe more); it is the desk\'s text, nothing to do here' % (ln, kind))
        else:
            E.append('line %d: %s outside the theorem statement (a numeral longer than 20 digits is refused: use a list of 64-bit words)' % (ln, kind))
    return E, W


class FootprintSampler:
    """peak phys_footprint (anonymous memory, compressed and swapped pages included; mapped .olean files are
    not counted) of the lean processes under a process tree, sampled twice a second with proc_pid_rusage."""

    def __init__(self, root_pid):
        import ctypes, threading
        self.root, self.peak, self.stop = root_pid, 0, False
        try:
            self.lib = ctypes.CDLL('/usr/lib/libproc.dylib')

            class RU(ctypes.Structure):
                _fields_ = [('uuid', ctypes.c_uint8 * 16)] + [(n, ctypes.c_uint64) for n in (
                    'user_time', 'system_time', 'pkg_idle_wkups', 'interrupt_wkups', 'pageins', 'wired_size',
                    'resident_size', 'phys_footprint', 'proc_start_abstime', 'proc_exit_abstime', 'child_user_time',
                    'child_system_time', 'child_pkg_idle_wkups', 'child_interrupt_wkups', 'child_pageins',
                    'child_elapsed_abstime', 'diskio_bytesread', 'diskio_byteswritten')]
            self.RU, self.ctypes = RU, ctypes
        except Exception:
            self.lib = None
        self.th = threading.Thread(target=self.run, daemon=True)
        self.th.start()

    def run(self):
        while not self.stop and self.lib is not None:
            try:
                out = subprocess.run(['ps', '-Ao', 'pid=,ppid=,comm='], capture_output=True, text=True).stdout
                kids, comm = {}, {}
                for line in out.splitlines():
                    q = line.split(None, 2)
                    if len(q) == 3:
                        kids.setdefault(int(q[1]), []).append(int(q[0]))
                        comm[int(q[0])] = q[2]
                stack, tot = [self.root], 0
                while stack:
                    x = stack.pop()
                    stack.extend(kids.get(x, []))
                    if os.path.basename(comm.get(x, '')) == 'lean':
                        ri = self.RU()
                        if self.lib.proc_pid_rusage(x, 2, self.ctypes.byref(ri)) == 0:
                            tot += ri.phys_footprint
                self.peak = max(self.peak, tot)
            except Exception:
                pass
            time.sleep(0.5)

    def done(self):
        self.stop = True
        return self.peak / 2 ** 30 if self.peak else None


def find_module(text):
    m = re.search(r'^theorem PEqualNP\.Outside\.([A-Za-z0-9_]+)', text, re.M)
    return m.group(1) if m else None


def main():
    a = sys.argv[1:]
    allowed = ['PEqualNP.Defs']
    cores, mem, tmax = 2, 10.0, 2400
    lint_only = keep = False
    numerals = 'strict'
    real = False
    keep_file = False
    in_slot = False
    stmt_file = None
    files = []
    while a:
        x = a.pop(0)
        if x == '--allow-import': allowed.append(a.pop(0))
        elif x == '--statement-file': stmt_file = a.pop(0)
        elif x == '--lint-only': lint_only = True
        elif x == '--numerals': numerals = a.pop(0)
        elif x == '--real': real = True
        elif x == '--keep-name': keep = True
        elif x == '--keep-file': keep_file = True
        elif x == '--in-slot': in_slot = True
        elif x == '-c': cores = int(a.pop(0))
        elif x == '-m': mem = float(a.pop(0))
        elif x == '-t': tmax = int(a.pop(0))
        elif x in ('-h', '--help'): print(__doc__); sys.exit(0)
        else: files.append(x)
    if len(files) != 1:
        print(__doc__); sys.exit(2)
    path = files[0]
    raw = open(path, 'rb').read()
    text = raw.decode('utf-8', 'replace')
    mod = find_module(text)
    if not mod:
        print('LINT FAIL: no line `theorem PEqualNP.Outside.<Module> ...` in the file'); print('FAIL'); sys.exit(1)
    statement = None
    if stmt_file:
        statement = open(stmt_file, encoding='utf-8').read().strip()
        m = re.match(r'theorem\s+(\S+)\s*:\s*', statement)
        if m:
            statement = statement[m.end():]
            d = 0
            for j, c in enumerate(statement):
                if c in '([{⟨': d += 1
                elif c in ')]}⟩': d -= 1
                elif d == 0 and statement.startswith(':=', j):
                    statement = statement[:j]; break
    E, W = lint(raw, mod, allowed, statement, numerals)
    for w in W:
        print('lint warning: ' + w)
    for e in E[:40]:
        print('lint error: ' + e)
    print('LINT %s  (%d bytes, module PEqualNP.Outside.%s, %d error(s), %d warning(s))' % ('FAIL' if E else 'ok', len(raw), mod, len(E), len(W)))
    if E:
        print('FAIL'); sys.exit(1)
    if lint_only:
        print('PASS (lint only, not built)'); sys.exit(0)

    lean_dir = os.path.join(SANDBOX, 'lean')
    if not os.path.exists(os.path.join(lean_dir, '.lake', 'packages', 'mathlib', '.lake', 'build', 'lib', 'lean', 'Mathlib.olean')):
        print('CANNOT JUDGE: the sandbox %s is missing or has no prebuilt Mathlib (make it with: git clone %s %s, then run `lake exe cache get` in its lean/ directory)' % (SANDBOX, MAIN_REPO, SANDBOX)); sys.exit(3)
    bmod = mod
    btext = text
    if os.path.exists(os.path.join(MAIN_REPO, 'lean', 'PEqualNP', 'Outside', mod + '.lean')) and not keep:
        bmod = mod + '_lc'
        btext = re.sub(r'(?<![A-Za-z0-9_])' + re.escape(mod) + r'(?![A-Za-z0-9])', lambda m_: bmod, text)
        print('note: %s is already on main; building the copy as %s' % (mod, bmod))
    dest = os.path.join(lean_dir, 'PEqualNP', 'Outside', bmod + '.lean')
    if not keep_file:   # the sandbox keeps no copy of a judged file (its build output stays under .lake/build)
        import atexit
        atexit.register(lambda: os.path.exists(dest) and os.remove(dest))
    lock = open(os.path.join(SANDBOX, '.leancheck.lock'), 'w')
    fcntl.flock(lock, fcntl.LOCK_EX)
    with open(dest, 'w', encoding='utf-8', newline='\n') as f:
        f.write(btext)
    # always a real build: drop what an earlier build of the same module left (lake would only replay it)
    import glob
    for sub in ('lib/lean', 'ir'):
        for old in glob.glob(os.path.join(lean_dir, '.lake', 'build', sub, 'PEqualNP', 'Outside', bmod + '.*')):
            try: os.remove(old)
            except OSError: pass
    env = dict(os.environ, LEAN_NUM_THREADS=str(cores), LAKE_ARTIFACT_CACHE='false')
    for k in list(env):
        if re.match(r'^(LAKE_(?!ARTIFACT_CACHE)|LEAN_(?!NUM_THREADS)|ELAN_TOOLCHAIN$)', k):
            del env[k]
    slot = [] if in_slot else [os.path.join(ROOT, 'bin', 'pnprun'), '-c', str(cores), '-m', str(mem), '-t', str(tmax), '--']
    slot1 = [] if in_slot else [os.path.join(ROOT, 'bin', 'pnprun'), '-c', '1', '-m', str(mem), '-t', '600', '--']
    cmd = slot + ['/usr/bin/time', '-l', 'lake', 'build', 'PEqualNP.Outside.' + bmod]
    t0 = time.time()
    p = subprocess.Popen(cmd, cwd=lean_dir, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, start_new_session=True)
    out = []
    net = None
    sampler = FootprintSampler(p.pid)
    for line in p.stdout:
        out.append(line)
        if re.search(r'(Building|Built|Compiling) Mathlib\b|: cloning |: updating |[Ff]etching|[Dd]ownloading|git clone', line) and 'Replayed' not in line:
            net = line.strip()
            try: os.killpg(p.pid, 9)
            except Exception: pass
            break
    rc = p.wait()
    fp = sampler.done()
    fp_s = '%.2f GB' % fp if fp is not None else 'n/a'
    wall = time.time() - t0
    log = ''.join(out)
    logdir = os.path.join(ROOT, 'runs', 'ckt2lean')
    os.makedirs(logdir, exist_ok=True)
    logpath = os.path.join(logdir, 'leancheck_%s.log' % bmod)
    open(logpath, 'w').write(log)
    if net:
        print('CANNOT JUDGE: lake started to fetch or to compile Mathlib; stopped at once. Line: ' + net[:200]); sys.exit(3)
    rss = re.search(r'(\d+)\s+maximum resident set size', log)
    rss_gb = int(rss.group(1)) / 2 ** 30 if rss else None
    killed = re.search(r'pnprun: killing job \(([^)]*)\)', log)
    errs = [l.rstrip() for l in log.split('\n') if re.match(r'^error[: ]', l)]
    ok = rc == 0 and 'Build completed successfully' in log
    tm = re.search(r'([0-9.]+) real\s+([0-9.]+) user\s+([0-9.]+) sys', log)
    cpu = ('%.1f s' % (float(tm.group(2)) + float(tm.group(3)))) if tm else 'n/a'
    print('BUILD %s  wall %.1f s (incl. waiting for a slot)  lake %s s real, cpu %s  peak RSS %s, peak footprint %s  (log: %s)'
          % ('ok' if ok else 'FAIL', wall, tm.group(1) if tm else 'n/a', cpu, '%.2f GB' % rss_gb if rss_gb is not None else 'n/a', fp_s, logpath))
    if killed:
        print('  killed by pnprun: ' + killed.group(1))
    for e in errs[:12]:
        print('  ' + e[:400])
    if not ok:
        print('FAIL'); sys.exit(1)
    # axioms the theorem rests on (a throwaway file outside the judged one)
    ax_src = os.path.join(lean_dir, 'LeancheckAxioms_%s.lean' % bmod)
    open(ax_src, 'w').write('import PEqualNP.Outside.%s\n#print axioms PEqualNP.Outside.%s\n' % (bmod, bmod))
    try:
        r = subprocess.run(slot1 + ['lake', 'env', 'lean', ax_src], cwd=lean_dir, env=env, capture_output=True, text=True)
    finally:
        os.remove(ax_src)
    axout = (r.stdout + r.stderr).strip()
    m = re.search(r'depends on axioms: \[([^\]]*)\]', axout.replace('\n', ' '))
    axioms = [x.strip() for x in m.group(1).split(',')] if m else ([] if 'does not depend on any axioms' in axout else None)
    if axioms is None:
        print('AXIOMS could not be read: ' + axout[-300:]); print('FAIL'); sys.exit(1)
    bad = [x for x in axioms if x not in ('propext', 'Classical.choice', 'Quot.sound')]
    print('AXIOMS %s  [%s]' % ('FAIL' if bad else 'ok', ', '.join(axioms)))
    if bad:
        print('FAIL'); sys.exit(1)
    if real:
        # the project's own checker, from the sandbox copy: tools/check-lean.mjs <file> <statement> check
        if statement is None:
            print('REAL CHECK needs --statement-file'); print('FAIL'); sys.exit(2)
        home = os.path.join(ROOT, '.cache', 'pequalnp-home')
        os.makedirs(home, exist_ok=True)
        open(os.path.join(home, 'build-jobs.conf'), 'w').write('%d\n' % cores)
        open(os.path.join(home, 'build-slots.conf'), 'w').write('1\n')
        st_path = os.path.join(home, 'statement_%s.txt' % bmod)
        open(st_path, 'w', encoding='utf-8').write(statement.strip() + '\n')
        env2 = dict(env, PEQUALNP_HOME=home, PEQUALNP_REAL_LAKE=shutil.which('lake') or 'lake')
        env2.pop('PEQUALNP_REPO_ROOT', None)
        env2.pop('PEQUALNP_IN_QUEUE', None)
        t1 = time.time()
        r = subprocess.run(slot + ['/usr/bin/time', '-l', 'node', os.path.join(SANDBOX, 'tools', 'check-lean.mjs'), dest, st_path, 'check'],
                           cwd=SANDBOX, env=env2, capture_output=True, text=True)
        wall2 = time.time() - t1
        rlog = r.stdout + r.stderr
        open(os.path.join(logdir, 'realcheck_%s.log' % bmod), 'w').write(rlog)
        rss2 = re.search(r'(\d+)\s+maximum resident set size', rlog)
        verdict = [l for l in rlog.split('\n') if l.startswith(('ACCEPTED', 'REJECTED', 'CHECKER FAULT', 'CHECKER MEMORY'))]
        print('REAL CHECK (tools/check-lean.mjs of the sandbox copy): %s  wall %.1f s  peak RSS %s  exit %d'
              % (verdict[-1][:200] if verdict else 'no verdict line', wall2, '%.2f GB' % (int(rss2.group(1)) / 2 ** 30) if rss2 else 'n/a', r.returncode))
        if r.returncode != 0 or not (verdict and verdict[-1].startswith('ACCEPTED')):
            print('FAIL'); sys.exit(1)
    print('PASS  %s  build %s s real / %s cpu, peak RSS %s, peak footprint %s'
          % (os.path.basename(path), tm.group(1) if tm else '%.1f' % wall, cpu, '%.2f GB' % rss_gb if rss_gb is not None else 'n/a', fp_s))
    sys.exit(0)


if __name__ == '__main__':
    main()
