#!/usr/bin/env python3
"""ckt2lean -- turn a verified circuit (.ckt) into a Lean 4 proof file in the shape the pequalnp.com checker accepts.

  ckt2lean --unit L-meta-20580 --statement-file STMT.txt [--kind K] [--style S] SPEC CKT -o OUT.lean
  ckt2lean --from-kn specs/kn7.spec KN.ckt [--crown-out CROWN.ckt] [--unit U --statement-file STMT.txt -o OUT.lean]

  SPEC, CKT            formats of FORMAT.md. The circuit is first checked with bin/cktcheck (basis and size
                       bound read from the statement); nothing is written for a wrong circuit.
  --unit U             L-meta-20580 or L_meta_20580: theorem PEqualNP.Outside.L_meta_20580, helpers in
                       namespace PEqualNP.Outside.L_meta_20580_aux.
  --statement-file F   the posted statement, verbatim. A whole skeleton line
                       `theorem NAME : STATEMENT := ...` is also accepted (the part between the first ` : ` and the
                       top-level `:=` is used, untouched).
  --kind K             represents | represents-mono | represents-ao2 | tt | tt-mono | tt-multi
                       (default: read off the statement)
  --style S            auto | direct | inline | lib
                         direct  one term, `by decide +kernel` on the statement's own decidable form (shape of the
                                 accepted L_meta_19546; small graph units only)
                         inline  self-contained bit-column simulation in the _aux namespace (imports
                                 PEqualNP.Defs only, like the accepted L_meta_19034)
                         lib     shape of the accepted L_meta_20578: PEqualNP.Library.Helpers.PromiseColTree
                                 (only if the unit's gap lists that import; row-list graph statements only)
  --tt-proof P         auto | enum | expr   how a truth-table target is checked: enum = evaluate the statement's
                       function on all 2^n inputs in the kernel (any decidable right-hand side); expr = translate a
                       Boolean formula over `x i` into column operations (no enumeration; needed for n >= 14).
  --graph-check G      auto | rows | points   how a graph target is checked in the inline style: rows = the
                       statement is `fun u v : Fin n => (([r0, ...] : List ℕ).getD u.val 0).testBit v.val`; the
                       target column is built from the rows in closed form and compared once (fastest).
                       points = any decidable A: one bit test per pair (u, v) against `A u v`.
  --max S              size bound (default: read off the statement)
  --imports A,B        import lines to write instead of the style's default
  --name-suffix SFX    append SFX to the module/theorem name (sandbox round trips of units already on main)
  --body-only          write only the helper namespace block, a blank line, and the proof term that closes the
                       theorem (for pasting under the desk's own skeleton). Needed imports are printed on stderr.
  --chunk N            gates per `def gatesK` (default 64)
Exit status 0 = file written; 1 = circuit refused by cktcheck or statement/spec mismatch; 2 = usage.
"""
import argparse, os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, 'py'))
sys.path.insert(0, HERE)
import pnpfast  # noqa: E402

CLB = 'PEqualNP.CircuitLowerBounds'
MC = 'PEqualNP.MetaComplexity'


def die(msg, code=1):
    print('ckt2lean: ' + msg, file=sys.stderr)
    sys.exit(code)


# ------------------------------------------------------------------ statement handling
OPEN = {'(': ')', '[': ']', '{': '}', '⟨': '⟩'}
CLOSE = set(OPEN.values())


def top_find(s, pat, start=0):
    """index of the first occurrence of the literal `pat` at bracket depth 0, or -1"""
    depth = 0
    i = start
    while i < len(s):
        c = s[i]
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        elif depth == 0 and s.startswith(pat, i):
            return i
        i += 1
    return -1


def top_split(s, pat):
    out = []
    i = 0
    while True:
        j = top_find(s, pat, i)
        if j < 0:
            out.append(s[i:])
            return out
        out.append(s[i:j])
        i = j + len(pat)


def strip_parens(s):
    s = s.strip()
    while s.startswith('(') and s.endswith(')'):
        depth = 0
        ok = True
        for i, c in enumerate(s):
            if c in OPEN:
                depth += 1
            elif c in CLOSE:
                depth -= 1
                if depth == 0 and i != len(s) - 1:
                    ok = False
                    break
        if not ok:
            break
        s = s[1:-1].strip()
    return s


def read_statement(path):
    raw = open(path, encoding='utf-8').read()
    s = raw.strip()
    name = None
    m = re.match(r'theorem\s+(\S+)\s*:\s*', s)
    if m:
        name = m.group(1)
        s = s[m.end():]
        j = top_find(s, ':=')
        if j >= 0:
            s = s[:j]
    s = s.strip()
    if '"' in s or '\n\n' in s:
        die('the statement file does not hold one plain Lean term')
    return s, name


def infer_kind(stmt):
    if 'RepSize2AtMost' in stmt or ('Represents' in stmt and 'IsAO2' in stmt):
        return 'represents-ao2'
    if 'RepSizeAtMost' in stmt:
        return 'represents-mono'
    if 'Represents' in stmt:
        return 'represents-mono' if 'Monotone2' in stmt else 'represents'
    if '.wires' in stmt:
        return 'tt-multi'
    if 'HasCircuitSize' in stmt:
        return 'tt'
    if '.eval' in stmt:
        return 'tt-mono' if 'Monotone2' in stmt else 'tt'
    die('cannot tell the kind of unit from the statement; pass --kind')


def infer_bound(stmt):
    m = re.search(r'\.size\s*≤\s*(\d+)', stmt)
    if m:
        return int(m.group(1))
    core = strip_parens(stmt)
    m = re.search(r'(?:RepSizeAtMost|RepSize2AtMost|HasCircuitSize)\b.*?(\d+)\s*$', core, re.S)
    if m:
        return int(m.group(1))
    return None


def basis_of(kind, stmt):
    if kind == 'represents-ao2':
        return 'ao2'
    if kind in ('represents-mono', 'tt-mono'):
        return 'ao'
    if kind == 'tt-multi' and 'Monotone2' in stmt:
        return 'ao'
    return 'aon'


# ------------------------------------------------------------------ Boolean formulas over `x i`
class BoolParseError(Exception):
    pass


TOK = re.compile(r'\s*(&&|\|\||\^\^|!|\(|\)|[A-Za-z_][A-Za-z0-9_.]*|\d+)')


def parse_bool(text, var):
    """parse a Lean Bool term over `var i` with &&, ||, ^^, !, xor, true, false. Returns an AST or raises."""
    toks = []
    pos = 0
    text = text.strip()
    while pos < len(text):
        m = TOK.match(text, pos)
        if not m:
            raise BoolParseError('cannot read: ' + text[pos:pos + 20])
        toks.append(m.group(1))
        pos = m.end()
    p = [0]

    def peek():
        return toks[p[0]] if p[0] < len(toks) else None

    def take(t=None):
        x = peek()
        if x is None or (t is not None and x != t):
            raise BoolParseError('expected %s' % t)
        p[0] += 1
        return x

    def atom():
        x = peek()
        if x == '(':
            take()
            if peek() is not None and peek().isdigit():
                raise BoolParseError('number in term position')
            e = or_e()
            take(')')
            return e
        if x in ('true', 'Bool.true'):
            take()
            return ('const', True)
        if x in ('false', 'Bool.false'):
            take()
            return ('const', False)
        if x == var:
            take()
            y = peek()
            if y == '(':
                take()
                i = take()
                take(')')
            else:
                i = take()
            if not i.isdigit():
                raise BoolParseError('index is not a numeral')
            return ('var', int(i))
        if x in ('xor', 'Bool.xor'):
            take()
            a = atom()
            b = atom()
            return ('xor', a, b)
        raise BoolParseError('cannot read token %r' % x)

    def not_e():
        if peek() == '!':
            take()
            return ('not', not_e())
        return atom()

    def and_e():
        e = not_e()
        while peek() == '&&':
            take()
            e = ('and', e, not_e())
        return e

    def xor_e():
        e = and_e()
        while peek() == '^^':
            take()
            e = ('xor', e, and_e())
        return e

    def or_e():
        e = xor_e()
        while peek() == '||':
            take()
            e = ('or', e, xor_e())
        return e

    e = or_e()
    if p[0] != len(toks):
        raise BoolParseError('trailing text')
    return e


def bool_colval(e, cols, full):
    """the truth table of the formula as a big integer (bit p = value at point p)"""
    t = e[0]
    if t == 'const':
        return full if e[1] else 0
    if t == 'var':
        return cols[e[1]]
    if t == 'not':
        return full ^ bool_colval(e[1], cols, full)
    a, b = bool_colval(e[1], cols, full), bool_colval(e[2], cols, full)
    return (a & b) if t == 'and' else (a | b) if t == 'or' else (a ^ b)


def bool_maxvar(e):
    t = e[0]
    if t == 'const':
        return -1
    if t == 'var':
        return e[1]
    return max(bool_maxvar(x) for x in e[1:])


def bool_lean(e, var='x'):
    t = e[0]
    if t == 'const':
        return 'true' if e[1] else 'false'
    if t == 'var':
        return '%s %d' % (var, e[1])
    if t == 'not':
        return '(!%s)' % bool_lean(e[1], var)
    op = {'and': '&&', 'or': '||', 'xor': '^^'}[t]
    return '(%s %s %s)' % (bool_lean(e[1], var), op, bool_lean(e[2], var))


def bool_col(e, n):
    t = e[0]
    if t == 'const':
        return ('tmask %d' % n) if e[1] else '0'
    if t == 'var':
        return 'vcol %d %d' % (n, e[1])
    if t == 'not':
        return '(ncol %d (%s))' % (n, bool_col(e[1], n))
    op = {'and': '&&&', 'or': '|||', 'xor': '^^^'}[t]
    return '(%s %s %s)' % (bool_col(e[1], n), op, bool_col(e[2], n))


def eq_split(s):
    """split `LHS = RHS` at the first top-level single `=`"""
    depth = 0
    for i, c in enumerate(s):
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        elif c == '=' and depth == 0:
            prev = s[i - 1] if i else ' '
            nxt = s[i + 1] if i + 1 < len(s) else ' '
            if prev in '=!:<>≤≥' or nxt in '=>':
                continue
            return s[:i].strip(), s[i + 1:].strip()
    return None


def tt_targets(stmt, N, K, multi):
    """the right-hand sides of the statement, one per output: (text, ast or None). Never raises."""
    core = strip_parens(stmt)
    res = [None] * K
    m = re.search(r'∀\s*\(?\s*([A-Za-z_][A-Za-z0-9_]*)\s*:\s*Fin\s+(\d+)\s*→\s*Bool\s*\)?\s*,', core)
    if m:
        var, body = m.group(1), core[m.end():]
        if int(m.group(2)) != N:
            die('the statement speaks of Fin %s inputs, the spec of %d' % (m.group(2), N))
        body = strip_parens(body)
        parts = [strip_parens(x) for x in top_split(body, '∧')] if multi else [body]
        if multi and len(parts) != K:
            die('the statement has %d conjuncts after the quantifier, the spec has %d outputs' % (len(parts), K))
        for idx, part in enumerate(parts):
            sp = eq_split(part)
            if not sp:
                continue
            lhs, rhs = sp
            j = idx
            if multi:
                mm = re.search(r'getD\s*\(\s*[A-Za-z_][A-Za-z0-9_]*\s+(\d+)\s*\)', lhs)
                if not mm or int(mm.group(1)) != idx:
                    die('conjunct %d of the statement does not read output %d (o %d)' % (idx, idx, idx))
            rhs = strip_parens(rhs)
            mb = re.match(r'\(\s*fun\s+([A-Za-z_][A-Za-z0-9_]*)\s*(?::[^=]*)?=>(.*)\)\s*' + re.escape(var) + r'\s*$', rhs, re.S)
            v2, txt = (mb.group(1), mb.group(2)) if mb else (var, rhs)
            try:
                ast = parse_bool(txt, v2)
                if bool_maxvar(ast) >= N:
                    ast = None
            except BoolParseError:
                ast = None
            res[j] = ast
        return res
    m = re.search(r'HasCircuitSize\s+(\d+)\s+\(\s*fun\s+([A-Za-z_][A-Za-z0-9_]*)\s*(?::[^=]*)?=>(.*)\)\s*(\d+)\s*$', core, re.S)
    if m and not multi:
        try:
            ast = parse_bool(m.group(3), m.group(2))
            res[0] = ast if bool_maxvar(ast) < N else None
        except BoolParseError:
            pass
    return res


# ------------------------------------------------------------------ circuits
def run_cktcheck(spec, ckt, basis, maxsize):
    cmd = [os.path.join(ROOT, 'bin', 'cktcheck'), spec, ckt, '--basis', basis]
    if maxsize is not None:
        cmd += ['--max', str(maxsize)]
    r = subprocess.run(cmd, capture_output=True, text=True)
    line = (r.stdout + r.stderr).strip()
    print('cktcheck: ' + line.replace('\n', ' | '), file=sys.stderr)
    return r.returncode == 0


def kn_to_crown(n, gates, outs):
    """a circuit on n wires (0 on 1-hot, 1 on 2-hot inputs) -> a circuit representing the crown graph u != v:
    wires 0..n-1 left, n..2n-1 right, gates z_i = x_i OR y_i first (wires 2n..3n-1), then the given gates."""
    def w(i):
        return 2 * n + i if i < n else 3 * n + (i - n)
    g2 = [('or', [i, n + i]) for i in range(n)]
    g2 += [(op, [w(i) for i in ins]) for op, ins in gates]
    return 2 * n, g2, [w(outs[0])]


def gate_inline(op, ins):
    return '⟨GateOp.%s, [%s]⟩' % (op, ', '.join(map(str, ins)))


def gate_long(op, ins):
    return '{ op := %s.GateOp.%s, inputs := [%s] }' % (CLB, op, ', '.join(map(str, ins)))


def gate_defs(gates, chunk, per_line=6):
    """`def gatesK : List Gate := [...]` blocks and `def cktGates`"""
    out = []
    names = []
    for c in range(0, max(len(gates), 1), chunk):
        part = gates[c:c + chunk]
        nm = 'gates%d' % (c // chunk)
        names.append(nm)
        rows = [', '.join(gate_inline(op, ins) for op, ins in part[r:r + per_line]) for r in range(0, len(part), per_line)]
        out.append('def %s : List Gate := [\n  %s]\n' % (nm, ',\n  '.join(rows)))
    out.append('def cktGates : List Gate :=\n  %s\n' % ' ++ '.join(names))
    return '\n'.join(out)


def depth_for(wires):
    d = 1
    while (1 << d) < wires:
        d += 1
    return d


def prelude(*names):
    return '\n'.join(open(os.path.join(HERE, 'prelude_%s.lean' % n), encoding='utf-8').read().rstrip('\n') + '\n' for n in names)


# ------------------------------------------------------------------ emitters
class Out:
    def __init__(self, imports, body, term, mod, stmt):
        self.imports, self.body, self.term, self.mod, self.stmt = imports, body, term, mod, stmt

    def full(self):
        s = ''.join('import %s\n' % i for i in self.imports) + '\n'
        if self.body:
            s += self.body.rstrip('\n') + '\n\n'
        s += 'theorem PEqualNP.Outside.%s : %s :=\n%s\n' % (self.mod, self.stmt, self.term.rstrip('\n'))
        return s

    def body_only(self):
        return (self.body.rstrip('\n') + '\n\n' if self.body else '') + self.term.rstrip('\n') + '\n'


def emit_direct(a, kind, stmt, mod, N, gates, outs):
    basis = 'Monotone2' if kind == 'represents-mono' else 'FanInTwo'
    glist = ', '.join(gate_long(op, ins) for op, ins in gates)
    bproof = 'by decide +kernel' if kind == 'represents-ao2' else 'by simp [%s.%s]' % (MC, basis)
    term = ('  by exact ⟨({ gates := [%s], output := %d } : %s.Circuit), %s, by decide, by decide +kernel⟩'
            % (glist, outs[0], CLB, bproof))
    return Out(a.imports or ['PEqualNP.Defs'], '', term, mod, stmt)


def emit_lib(a, kind, stmt, mod, S, gates, outs):
    n, m = S['n'], S['m']
    Nexp = depth_for(n * m) if n * m > 1 else 0
    D = depth_for(n + m + len(gates))
    if kind == 'represents-ao2':
        die('the lib style has no IsAO2 form; use --style inline or direct', 2)
    snd = 'monotone2B_sound' if kind == 'represents-mono' else 'fanInTwoB_sound'
    rows = [', '.join(gate_inline(op, ins).replace('GateOp.', '.') for op, ins in gates[r:r + 6]) for r in range(0, len(gates), 6)]
    H = 'PEqualNP.Library.Helpers'
    term = '\n'.join([
        '  by',
        '    let C : %s.Circuit := ⟨[' % CLB,
        '      ' + ',\n      '.join(rows) + '], %d⟩' % outs[0],
        '    refine ⟨C, %s.Replay.%s ?_, ?_, ?_⟩' % (H, snd),
        '    · decide +kernel',
        '    · decide +kernel',
        '    · apply %s.PromiseColTree.represents_of_tcols (N := %d) (D := %d) (by decide) C' % (H, Nexp, D),
        '      · decide +kernel',
        '      · decide +kernel',
        '      · decide +kernel',
        '      · decide +kernel'])
    return Out(a.imports or ['PEqualNP.Defs', H + '.PromiseColTree'], '', term, mod, stmt)


# `fun u v : Fin n => (([r0, r1, ...] : List ℕ).getD u.val 0).testBit v.val` -- the row-list form of a graph
ROWS_SHAPE = re.compile(r'fun\s+([A-Za-z_][A-Za-z0-9_]*)\s+([A-Za-z_][A-Za-z0-9_]*)\s*:\s*Fin\s+\d+\s*=>\s*\(\s*\(\s*\[[0-9a-fA-FxX,\s]*\]\s*:\s*List\s+ℕ\s*\)\s*\.getD\s+\1\.val\s+0\s*\)\s*\.testBit\s+\2\.val')


def ns_block(aux, opens, parts):
    return ('namespace %s\n\nopen %s\n\n' % (aux, ' '.join(opens))) + '\n'.join(p.rstrip('\n') + '\n' for p in parts) + '\nend %s\n' % aux


def emit_inline_graph(a, kind, stmt, mod, S, gates, outs, bound):
    n, m = S['n'], S['m']
    D = depth_for(n + m + len(gates))
    aux = 'PEqualNP.Outside.%s_aux' % mod
    mono = kind == 'represents-mono'
    facts = [
        'def ckt : Circuit := ⟨cktGates, %d⟩\n' % outs[0],
        ('theorem hbasis : PEqualNP.TopForm.IsAO2 (%d + %d) ckt := by decide +kernel\n' % (n, m) if kind == 'represents-ao2' else
         'theorem hbasis : Monotone2 ckt := monotone2B_sound (by decide +kernel)\n' if mono else
         'theorem hbasis : FanInTwo ckt := fanInTwoB_sound (by decide +kernel)\n'),
        'theorem hsz : ckt.size ≤ %d := by decide +kernel\n' % bound,
        'theorem haon : aonB ckt = true := by decide +kernel\n',
        'theorem hcap : gcap %d %d %d ckt = true := by decide +kernel\n' % (n, m, D),
    ]
    body = ns_block(aux, [CLB, MC, 'PEqualNP.Represents'],
                    [prelude('core', 'graph'), gate_defs(gates, a.chunk)] + facts)
    check = a.graph_check
    if check == 'auto':
        check = 'rows' if ROWS_SHAPE.search(stmt) else 'points'
    if check == 'rows':
        term = ('  ⟨{x}.ckt, {x}.hbasis, {x}.hsz, {x}.represents_rows {D} {x}.ckt _ (by decide +kernel) {x}.haon {x}.hcap (by decide +kernel)⟩'
                .format(x=aux, D=D))
    else:
        term = ('  ⟨{x}.ckt, {x}.hbasis, {x}.hsz, {x}.represents_of {D} {x}.ckt _ {x}.haon {x}.hcap (by decide +kernel)⟩'
                .format(x=aux, D=D))
    return Out(a.imports or ['PEqualNP.Defs'], body, term, mod, stmt)


def emit_inline_tt(a, kind, stmt, mod, S, gates, outs, bound):
    N, K = S['N'], S['K']
    multi = kind == 'tt-multi'
    mono = basis_of(kind, stmt) == 'ao'
    D = depth_for(N + len(gates))
    aux = 'PEqualNP.Outside.%s_aux' % mod
    asts = tt_targets(stmt, N, K, multi)
    mode = a.tt_proof
    use_expr = []
    for j in range(K):
        if mode == 'enum':
            use_expr.append(False)
            if N >= 16 and j == 0:
                print('ckt2lean: warning: --tt-proof enum on 2^%d inputs: measured about 10 s and 0.8 GB per 2^14 points and output (27-gate formula); this will be long and large' % N, file=sys.stderr)
        elif mode == 'expr':
            if asts[j] is None:
                die('--tt-proof expr: the right-hand side of output %d is not a formula over `x i` with && || ^^ ! that I can read' % j)
            use_expr.append(True)
        else:
            use_expr.append(asts[j] is not None and N >= 14)
            if asts[j] is None and N >= 16:
                die('output %d: the right-hand side is not a formula over `x i` with && || ^^ ! that I can read, and enumerating 2^%d inputs in the kernel is too costly (measured: about 10 s and 0.8 GB per 2^14 points). Force it with --tt-proof enum, or extend parse_bool.' % (j, N))
    # the spec and the formula must agree where the formula could be read
    for j in range(K):
        if asts[j] is not None and bool_colval(asts[j], S['cols'], (1 << S['P']) - 1) != S['tgt'][j]:
            die('output %d: the formula in the statement is not the function of the spec' % j)
    facts = [
        'def ckt : Circuit := ⟨cktGates, %d⟩\n' % (outs[0] if not multi else 0),
        ('theorem hbasis : Monotone2 ckt := monotone2B_sound (by decide +kernel)\n' if mono else
         'theorem hbasis : FanInTwo ckt := fanInTwoB_sound (by decide +kernel)\n'),
        'theorem hsz : ckt.size ≤ %d := by decide +kernel\n' % bound,
        'theorem haon : aonB ckt = true := by decide +kernel\n',
        'theorem hcap : tcap %d %d ckt = true := by decide +kernel\n' % (N, D),
    ]
    if multi:
        facts.append('def outs : Fin %d → ℕ := fun j => ([%s] : List ℕ).getD j.val 0\n' % (K, ', '.join(map(str, outs))))
    simpset = 'Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, Nat.zero_testBit, vcol_bit, ncol_bit, tmask_bit'
    pieces = []
    for j in range(K):
        wire = '(outs %d)' % j if multi else 'ckt.output'
        if use_expr[j]:
            facts.append('def ecol%d : ℕ := %s\n' % (j, bool_col(asts[j], N)))
            facts.append('theorem hE%d : ∀ x : Fin %d → Bool, ecol%d.testBit (tableIndex x) = %s := by\n  intro x\n  simp only [ecol%d, %s]\n'
                         % (j, N, j, bool_lean(asts[j]), j, simpset))
            facts.append('theorem hv%d : (wcol (tmask %d) %d ckt (ttCols %d) %s == ecol%d) = true := by decide +kernel\n'
                         % (j, N, D, N, wire, j))
            if multi:
                facts.append('theorem hout%d : ∀ x : Fin %d → Bool, (ckt.wires (List.ofFn x)).getD (outs %d) false = %s :=\n  wire_of_expr %d ckt (outs %d) ecol%d _ haon hcap hv%d hE%d\n'
                             % (j, N, j, bool_lean(asts[j]), D, j, j, j, j))
                pieces.append('%s.hout%d' % (aux, j))
            else:
                facts.append('theorem hout : ∀ x : Fin %d → Bool, ckt.eval (List.ofFn x) = %s :=\n  eval_of_expr %d ckt ecol0 _ haon hcap hv0 hE0\n'
                             % (N, bool_lean(asts[j]), D))
                pieces.append('%s.hout' % aux)
        else:
            if multi:
                pieces.append('({x}.wire_of_enum {D} {x}.ckt ({x}.outs {j}) _ {x}.haon {x}.hcap (by decide +kernel))'.format(x=aux, D=D, j=j))
            else:
                pieces.append('{x}.eval_of_enum {D} {x}.ckt _ {x}.haon {x}.hcap (by decide +kernel)'.format(x=aux, D=D))
    body = ns_block(aux, [CLB, MC], [prelude('core', 'tt'), gate_defs(gates, a.chunk)] + facts)
    if multi:
        allp = pieces[-1]
        for q in reversed(pieces[:-1]):
            allp = '%s.and_all %s (%s)' % (aux, q, allp) if allp.startswith(aux + '.and_all') else '%s.and_all %s %s' % (aux, q, allp)
        term = '  ⟨{x}.ckt, {x}.outs, {x}.hbasis, {x}.hsz, {p}⟩'.format(x=aux, p=allp)
    else:
        term = '  ⟨{x}.ckt, {x}.hbasis, {x}.hsz, {p}⟩'.format(x=aux, p=pieces[0])
    return Out(a.imports or ['PEqualNP.Defs'], body, term, mod, stmt)


# ------------------------------------------------------------------ main
def main():
    ap = argparse.ArgumentParser(add_help=False)
    ap.add_argument('-h', '--help', action='store_true')
    ap.add_argument('--unit')
    ap.add_argument('--statement-file')
    ap.add_argument('--kind', choices=['represents', 'represents-mono', 'represents-ao2', 'tt', 'tt-mono', 'tt-multi'])
    ap.add_argument('--style', default='auto', choices=['auto', 'direct', 'inline', 'lib'])
    ap.add_argument('--tt-proof', default='auto', choices=['auto', 'enum', 'expr'])
    ap.add_argument('--graph-check', default='auto', choices=['auto', 'rows', 'points'])
    ap.add_argument('--max', type=int)
    ap.add_argument('--imports')
    ap.add_argument('--name-suffix', default='')
    ap.add_argument('--body-only', action='store_true')
    ap.add_argument('--chunk', type=int, default=64)
    ap.add_argument('--from-kn', action='store_true')
    ap.add_argument('--crown-out')
    ap.add_argument('--crown-spec')
    ap.add_argument('-o', '--out')
    ap.add_argument('spec', nargs='?')
    ap.add_argument('ckt', nargs='?')
    a = ap.parse_args()
    if a.help or not a.spec or not a.ckt:
        print(__doc__)
        sys.exit(0 if a.help else 2)
    a.imports = [x.strip() for x in a.imports.split(',') if x.strip()] if a.imports else None

    stmt = name = None
    if a.statement_file:
        stmt, name = read_statement(a.statement_file)
    spec_path, ckt_path = a.spec, a.ckt

    if a.from_kn:
        KS = pnpfast.load_spec(spec_path)
        n = KS['N']
        if not run_cktcheck(spec_path, ckt_path, 'ao', None):
            die('the K(n) circuit is refused by cktcheck; nothing written')
        kN, kg, ko = pnpfast.load_ckt(ckt_path)
        if kN != n or len(ko) != 1:
            die('the K(n) circuit must have %d inputs and one output' % n)
        cN, cg, co = kn_to_crown(n, kg, ko)
        crown_spec = a.crown_spec or os.path.join(os.path.dirname(os.path.abspath(spec_path)), 'crown%d.spec' % n)
        crown_out = a.crown_out or (os.path.splitext(a.out)[0] + '.crown%d.ckt' % n if a.out else None)
        if not crown_out:
            die('--from-kn needs --crown-out CROWN.ckt (or -o OUT.lean)', 2)
        pnpfast.save_ckt(crown_out, cN, cg, co, 'crown%d from a K(%d) circuit of %d gates: z_i = x_i OR y_i on wires %d..%d, then the K circuit'
                         % (n, n, len(kg), 2 * n, 3 * n - 1))
        bound = a.max if a.max is not None else (infer_bound(stmt) if stmt else None)
        if not run_cktcheck(crown_spec, crown_out, 'ao', bound):
            die('the crown circuit is refused by cktcheck (kept at %s for inspection); no Lean written' % crown_out)
        print('ckt2lean: wrote %s (%d gates)' % (crown_out, len(cg)), file=sys.stderr)
        if not stmt:
            return
        spec_path, ckt_path = crown_spec, crown_out

    if not stmt:
        die('--statement-file is required', 2)
    unit = a.unit or name
    if not unit:
        die('--unit is required (or give the whole `theorem NAME : ...` skeleton in the statement file)', 2)
    mod = unit.split('.')[-1].replace('-', '_') + a.name_suffix
    if not re.fullmatch(r'L_[a-z0-9_]+', mod) or mod.endswith('_aux'):
        die('bad unit name %r (want L-meta-12345)' % unit, 2)
    if not a.out:
        die('-o OUT.lean is required', 2)

    kind = a.kind or infer_kind(stmt)
    bound = a.max if a.max is not None else infer_bound(stmt)
    if bound is None:
        die('cannot read the size bound off the statement; pass --max')
    basis = basis_of(kind, stmt)
    S = pnpfast.load_spec(spec_path)
    if kind.startswith('represents') != (S['kind'] == 'graph'):
        die('kind %s does not fit a spec of type %s' % (kind, S['kind']))
    if not kind.startswith('represents') and S['kind'] != 'tt':
        die('truth-table kinds need a spec of type tt')
    if (kind == 'tt-multi') != (S['K'] > 1) and kind != 'tt-multi':
        die('the spec has %d outputs; use --kind tt-multi' % S['K'])
    if not run_cktcheck(spec_path, ckt_path, basis, bound):
        die('the circuit is refused by cktcheck (basis %s, at most %d gates); nothing written' % (basis, bound))
    N, gates, outs = pnpfast.load_ckt(ckt_path)
    if N != S['N'] or len(outs) != S['K']:
        die('circuit and spec disagree on inputs/outputs')
    if pnpfast.check(S, N, gates, outs) != 0:
        die('the Python reference evaluator disagrees with cktcheck; nothing written')
    for op, ins in gates:
        if op not in ('and', 'or', 'not') or len(ins) > 2:
            die('gate outside the basis')

    style = a.style
    if kind.startswith('represents'):
        mdim = re.search(r'Fin\s+(\d+)', stmt)
        if mdim and int(mdim.group(1)) != S['n']:
            die('the statement speaks of Fin %s, the spec has n = %d' % (mdim.group(1), S['n']))
        if style == 'auto':
            style = 'direct' if S['n'] * S['m'] <= 100 and len(gates) <= 64 else 'inline'
        if style == 'direct':
            o = emit_direct(a, kind, stmt, mod, N, gates, outs)
        elif style == 'lib':
            if not ROWS_SHAPE.search(stmt):
                die('the lib style needs a row-list graph statement (fun u v : Fin n => (([..] : List ℕ).getD u.val 0).testBit v.val)', 2)
            o = emit_lib(a, kind, stmt, mod, S, gates, outs)
        else:
            o = emit_inline_graph(a, kind, stmt, mod, S, gates, outs, bound)
    else:
        if style in ('direct', 'lib'):
            die('truth-table kinds are written in the inline style only', 2)
        style = 'inline'
        o = emit_inline_tt(a, kind, stmt, mod, S, gates, outs, bound)

    text = o.body_only() if a.body_only else o.full()
    if '"' in text:
        die('internal error: a double quote in the output')
    with open(a.out, 'w', encoding='utf-8', newline='\n') as f:
        f.write(text)
    print('ckt2lean: wrote %s  (%d bytes, kind %s, style %s, %d gates, bound %d, theorem PEqualNP.Outside.%s)'
          % (a.out, len(text.encode('utf-8')), kind, style, len(gates), bound, mod), file=sys.stderr)
    if a.body_only:
        print('ckt2lean: imports needed: ' + ', '.join(o.imports), file=sys.stderr)
    # the format rules of the checker, on the whole file (also when only the body was asked for)
    import leancheck
    errs, warns = leancheck.lint(o.full().encode('utf-8'), mod, o.imports, stmt)
    for w in warns:
        print('ckt2lean: lint warning: ' + w, file=sys.stderr)
    for e in errs:
        print('ckt2lean: LINT ERROR: ' + e, file=sys.stderr)
    if errs:
        die('the file was written but breaks the format rules above')


if __name__ == '__main__':
    main()
