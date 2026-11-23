#!/usr/bin/env bash
set -euo pipefail
shard=$1
case "$shard" in 14|15) ;; *) exit 2 ;; esac
out="$RUNNER_TEMP/shard$shard"
mkdir -p "$out"
sha256sum research/search1343.py
python3 research/search1343.py --shard "$shard" --mode normal --timeout 600 \
  --cadical "$RUNNER_TEMP/solver/usr/bin/cadical" --dimacs "$out/search.cnf" \
  --proof "$out/proof.drat" --witness "$out/witness.json" | tee "$out/search.log"
sha256sum "$out/search.cnf"
if grep -Fxq UNSAT "$out/search.log"; then
  "$RUNNER_TEMP/drat-check" "$out/search.cnf" "$out/proof.drat" > "$out/check.log"
  grep -Fx 's VERIFIED' "$out/check.log"
  sha256sum "$out/proof.drat"
fi
