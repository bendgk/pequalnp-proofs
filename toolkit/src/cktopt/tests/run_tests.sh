#!/bin/sh
# cktopt validation: random bloated circuits, DNF circuits for the tt/points specs, degenerate Lean-style gates.
# Every run here is single-threaded and takes a few seconds (README.md: outside bin/pnprun exactly one thread).
# With MT=1 the two multi-threaded checks are added and they go through bin/pnprun -c 2 (waits for free slots).
#   usage: [MT=1] run_tests.sh [WORKDIR]
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
WORK="${1:-${TMPDIR:-/tmp}/cktopt_tests}"
mkdir -p "$WORK"
OPT="$ROOT/bin/cktopt"; CHK="$ROOT/bin/cktcheck"; PY=python3
fail=0; n=0
one() {  # spec in basis extra-args...
  spec="$1"; in="$2"; basis="$3"; shift 3
  out="$WORK/out_$n.ckt"; n=$((n+1))
  if ! "$OPT" "$spec" "$in" -o "$out" --basis "$basis" "$@" > "$WORK/log_$n.txt" 2>&1; then echo "FAIL (cktopt exit) $spec $in"; tail -3 "$WORK/log_$n.txt"; fail=1; return; fi
  if grep -q "INTERNAL\|inconsistent\|wrong circuit" "$WORK/log_$n.txt"; then echo "FAIL (internal error reported) $spec $in"; grep "INTERNAL\|inconsistent\|wrong" "$WORK/log_$n.txt" | head -3; fail=1; fi
  if ! "$CHK" "$spec" "$out" --basis "$basis" -q; then echo "FAIL (cktcheck) $spec $in"; fail=1; return; fi
  a=$(grep -c '^\(and\|or\|not\)' "$in"); b=$(grep -c '^\(and\|or\|not\)' "$out")
  if [ "$b" -gt "$a" ]; then echo "FAIL (grew $a -> $b) $spec $in"; fail=1; return; fi
  echo "ok   $(basename "$spec") $basis $* : $a -> $b"
}
# 1. random circuits, both bases, with and without don't-cares, single and multi output
for seed in 1 2 3 4 5 6 7 8; do
  basis=aon; [ $((seed % 2)) -eq 0 ] && basis=ao
  dc=0; [ $((seed % 3)) -eq 0 ] && dc=0.3
  K=1; [ $((seed % 4)) -eq 0 ] && K=3
  $PY "$HERE/gen.py" random $seed 10 60 $K 300 $dc "$WORK" $basis > /dev/null
  one "$WORK/rand_$seed.spec" "$WORK/rand_$seed.ckt" $basis --rounds 6 --round-work 3e7 --seed $seed --debug
done
# larger random case, time budget
$PY "$HERE/gen.py" random 99 16 300 2 3000 0.1 "$WORK" aon > /dev/null
one "$WORK/rand_99.spec" "$WORK/rand_99.ckt" aon --time 4 -j 1
# 2. naive DNF circuits for truth-table / points specs (nothing graph-specific)
for s in match3 cyc7 kn5 kn6 mm2; do
  $PY "$HERE/gen.py" dnf "$ROOT/specs/$s.spec" "$WORK/dnf_$s.ckt" > /dev/null
  one "$ROOT/specs/$s.spec" "$WORK/dnf_$s.ckt" aon --time 4
done
# 3. each level separately on one case (debug checks on)
for L in 1 2 3 4 5; do one "$ROOT/specs/cyc7.spec" "$WORK/dnf_cyc7.ckt" aon --level $L --rounds 4 --round-work 3e7 --debug; done
# 3b. the direct-scan path (no point index), used automatically for very large specs
one "$ROOT/specs/cyc7.spec" "$WORK/dnf_cyc7.ckt" aon --no-index --rounds 4 --round-work 3e7 --debug
one "$WORK/rand_3.spec" "$WORK/rand_3.ckt" aon --no-index --rounds 4 --round-work 3e7 --debug
one "$ROOT/specs/cand32.spec" "$ROOT/seeds/cand32_207.ckt" aon --no-index --rounds 3 --round-work 3e7 --debug
# 3c. experimental moves keep the circuit correct too
one "$ROOT/specs/cand32.spec" "$ROOT/seeds/cand32_207.ckt" aon --rar 0.5 --side-mode 2 --pair-every 2 --rounds 3 --round-work 3e7 --debug
one "$ROOT/specs/match3.spec" "$WORK/dnf_match3.ckt" aon --rar 0.5 --max-terms 8 --rounds 4 --round-work 3e7 --debug
# 3d. set-space sharing optimiser alone, and with partner exchanges / annealing
one "$ROOT/specs/cand32.spec" "$ROOT/seeds/cand32_207.ckt" aon --share-only 3e7
one "$ROOT/specs/match3.spec" "$WORK/dnf_match3.ckt" aon --share-only 3e7
one "$WORK/rand_99.spec" "$WORK/rand_99.ckt" aon --share-only 3e7
one "$ROOT/specs/cand32.spec" "$ROOT/seeds/cand32_207.ckt" aon --share-repair 0.2 --share-temp 1 --share-work 2e7 --rounds 4 --round-work 3e7 --debug
# 4. degenerate gates (copies, constants, forward references) are normalised away
$PY "$HERE/gen.py" degenerate 5 "$ROOT/specs/cand32.spec" "$ROOT/seeds/cand32_207.ckt" "$WORK/deg32.ckt" > /dev/null
one "$ROOT/specs/cand32.spec" "$WORK/deg32.ckt" aon --rounds 3 --round-work 3e7 --debug
one "$ROOT/specs/cand32.spec" "$ROOT/seeds/cand32_207.ckt" ao --rounds 3 --round-work 3e7 --debug
# 5. determinism: same seed and rounds -> identical output
det() {  # threads, launcher prefix...
  j="$1"; shift
  "$@" "$OPT" "$ROOT/specs/cand32.spec" "$ROOT/seeds/cand32_207.ckt" -o "$WORK/d1.ckt" --rounds 5 --round-work 3e7 --seed 7 -j $j -q > /dev/null 2>&1
  "$@" "$OPT" "$ROOT/specs/cand32.spec" "$ROOT/seeds/cand32_207.ckt" -o "$WORK/d2.ckt" --rounds 5 --round-work 3e7 --seed 7 -j $j -q > /dev/null 2>&1
  if cmp -s "$WORK/d1.ckt" "$WORK/d2.ckt"; then echo "ok   deterministic for fixed --seed/--rounds, -j $j"; else echo "FAIL determinism -j $j"; fail=1; fi
}
det 1
if [ "${MT:-0}" = 1 ]; then
  det 2 "$ROOT/bin/pnprun" -c 2 -m 2 -t 120 --
  n=$((n+1))
  "$ROOT/bin/pnprun" -c 2 -m 2 -t 120 -- "$OPT" "$WORK/rand_99.spec" "$WORK/rand_99.ckt" -o "$WORK/mt.ckt" --time 4 -j 2 > "$WORK/log_mt.txt" 2>&1
  if "$CHK" "$WORK/rand_99.spec" "$WORK/mt.ckt" -q; then echo "ok   rand_99 -j 2 via pnprun"; else echo "FAIL rand_99 -j 2"; fail=1; fi
fi
[ $fail -eq 0 ] && echo "ALL TESTS PASSED" || echo "SOME TESTS FAILED"
exit $fail
