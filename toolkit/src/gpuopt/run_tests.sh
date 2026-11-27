#!/bin/sh
# gpuopt self-test: every run uses --check (each GPU dispatch compared bit-exactly with the CPU reference kernels),
# every output goes through bin/cktcheck, and GPU runs are compared byte-for-byte with --cpu runs.
#   sh src/gpuopt/run_tests.sh WORKDIR      (single CPU thread, about 40 s; inputs from src/cktopt/tests/gen.py)
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
WORK=${1:?usage: run_tests.sh WORKDIR}
mkdir -p "$WORK"
GEN="python3 $ROOT/src/cktopt/tests/gen.py"
fail=0; n=0
run() {   # spec ckt basis rounds
  n=$((n + 1))
  g="$WORK/out_$n.gpu.ckt"; c="$WORK/out_$n.cpu.ckt"
  "$ROOT/bin/gpuopt" "$1" "$2" -o "$g" --basis "$3" --rounds "$4" --seed $n --two-every 2 --check -q > "$WORK/out_$n.txt" || { echo "FAIL run $n (gpu) $1"; fail=1; return; }
  "$ROOT/bin/gpuopt" "$1" "$2" -o "$c" --basis "$3" --rounds "$4" --seed $n --two-every 2 --cpu -q > /dev/null || { echo "FAIL run $n (cpu) $1"; fail=1; return; }
  "$ROOT/bin/cktcheck" "$1" "$g" --basis "$3" -q || { echo "FAIL run $n cktcheck $1"; fail=1; return; }
  tail -n +2 "$g" > "$WORK/a.txt"; tail -n +2 "$c" > "$WORK/b.txt"
  cmp -s "$WORK/a.txt" "$WORK/b.txt" || { echo "FAIL run $n: GPU and CPU results differ ($1)"; fail=1; return; }
  echo "ok  $(basename "$1") $(basename "$2") $3: $(grep -c -E '^(and|or|not)' "$2") -> $(cat "$WORK/out_$n.txt")"
}
for seed in 1 2 3 4; do
  for basis in aon ao; do
    K=1; dc=0.3; [ $seed -ge 3 ] && K=3 && dc=0
    $GEN random $seed 10 60 $K 300 $dc "$WORK" $basis > /dev/null
    cp "$WORK/rand_$seed.spec" "$WORK/r_${seed}_$basis.spec"; cp "$WORK/rand_$seed.ckt" "$WORK/r_${seed}_$basis.ckt"
    run "$WORK/r_${seed}_$basis.spec" "$WORK/r_${seed}_$basis.ckt" $basis 12
  done
done
for s in cyc7 match3 kn5 mm2; do
  $GEN dnf "$ROOT/specs/$s.spec" "$WORK/dnf_$s.ckt" > /dev/null
  run "$ROOT/specs/$s.spec" "$WORK/dnf_$s.ckt" aon 6
done
$GEN degenerate 5 "$ROOT/specs/cand32.spec" "$ROOT/seeds/cand32_207.ckt" "$WORK/deg32.ckt" > /dev/null
run "$ROOT/specs/cand32.spec" "$WORK/deg32.ckt" aon 10
run "$ROOT/specs/cand32.spec" "$ROOT/seeds/cand32_207.ckt" ao 10
[ $fail = 0 ] && echo "ALL $n TESTS PASSED" || echo "SOME TESTS FAILED"
exit $fail
