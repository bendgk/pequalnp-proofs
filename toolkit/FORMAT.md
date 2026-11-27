# Toolkit shared formats (contract for every tool here)

All tools read a SPEC (what must be computed, on which points) and read/write CIRCUITS.
Semantics mirror the Lean definitions in pequalnp-proofs/lean/PEqualNP/Defs/CircuitLowerBounds.lean EXACTLY.

## Circuit file (.ckt)  — text, '#' starts a comment
    inputs N            # wires 0..N-1 are the inputs
    and a b             # gate j (0-based, in file order) produces wire N+j
    or a b
    not a
    and                 # 0 inputs: constant true      (or with 0 inputs: constant false)
    or a                # 1 input: copy                (not with 0 inputs: true; not a b: reads a only)
    out w0 [w1 ...]     # output wire(s); K entries for a K-output spec
Lean semantics: a gate may name ANY wire index; a wire that does not exist yet (index >= N+j when gate j is
evaluated) reads false. An output wire that does not exist reads false. Every gate counts (NOT included).
size = number of gate lines. FanInTwo = ops in {and,or,not}, at most 2 inputs. Monotone2 = {and,or}, <=2 inputs.
IsAO2 (repSize2) = {and,or}, EXACTLY 2 inputs, each an earlier wire.

## Spec file (.spec) — text. Three kinds; all normalise to: N input wires, K outputs, P points,
## and each wire is a P-bit column (bit p = value of the wire at point p).
    type graph          # Represents A C : n left + m right wires, P = n*m points, point p = u*m+v
    n 32
    m 32
    rows f2bc7573 59092a9d ...     # n hex numbers; bit v of rows[u] = A u v.  (target bit p = A u v)
  input wire u (<n) is on exactly at points with left vertex u; wire n+v at points with right vertex v.

    type tt             # full truth table: P = 2^N, point index p = sum x_i 2^i  (Lean tableIndex)
    inputs 9
    outputs 1
    tt <hex>            # one line per output; hex of the 2^N-bit number whose bit p is f(point p)

    type points         # arbitrary point list (promise problems)
    inputs 7
    outputs 1
    p 1000000 0         # <N chars: wire 0 first> <K chars in {0,1,-}>   ('-' = don't care)

## Basis names used by tools
    ao   = AND/OR, fan-in <= 2 (Monotone2)          ao2 = AND/OR fan-in exactly 2 reading earlier wires (IsAO2)
    aon  = AND/OR/NOT, fan-in <= 2, NOT counted (FanInTwo)

## Shared code
    include/ckt.hpp     C++20 header: Spec/Circuit load+save, bit-parallel exact eval (pnp::eval), verify.
    py/pnpfast.py       Python mirror (slow reference evaluator + spec generators + Lean <-> .ckt).
Every search tool MUST re-verify any circuit it outputs with pnp::verify before printing it, and
`bin/cktcheck spec ckt` is the independent final check.
