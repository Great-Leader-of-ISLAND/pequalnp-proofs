#!/usr/bin/env bash
set -euo pipefail
shard=$1
case "$shard" in 14|15) ;; *) exit 2 ;; esac
out="$RUNNER_TEMP/shard$shard"
mkdir -p "$out"
case "$shard" in
  14) gap=L-meta-1343 ;;
  15) gap=L-meta-1342 ;;
esac
curl --retry 2 -fsS https://data.pequalnp.com/data/desk/gaps.json > "$out/public-desk.json"
python3 - "$gap" "$out/public-desk.json" <<'CHECK'
import json
import sys
gap, path = sys.argv[1:]
desk = json.load(open(path))
assert any(r['id'] == gap for r in desk['gaps']), f'{gap} closed; no search started'
assert not any(r['id'] == gap for r in desk['checked']), f'{gap} settled; no search started'
CHECK
sha256sum research/search1343v2.py
python3 research/search1343v2.py --shard "$shard" --mode normal --timeout 3900 \
  --cadical "$RUNNER_TEMP/solver/usr/bin/cadical" --dimacs "$out/search.cnf" \
  --proof "$out/proof.drat" --witness "$out/witness.json" | tee "$out/search.log"
sha256sum "$out/search.cnf"
if grep -Fxq UNSAT "$out/search.log"; then
  "$RUNNER_TEMP/drat-check" "$out/search.cnf" "$out/proof.drat" > "$out/check.log"
  grep -Fx 's VERIFIED' "$out/check.log"
  sha256sum "$out/proof.drat"
fi
