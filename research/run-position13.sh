#!/usr/bin/env bash
set -euo pipefail
position=$1
case "$position" in 13) task=L-meta-1343 ;; 15) task=L-meta-1342 ;; *) exit 2 ;; esac
dir="$RUNNER_TEMP/position$position"
mkdir "$dir"
curl --retry 2 -fsSL https://data.pequalnp.com/data/desk/gaps.json -o "$dir/desk.json"
python3 - "$dir/desk.json" "$task" "$position" <<'CHECK'
import json,sys
data=json.load(open(sys.argv[1]))
task=sys.argv[2]
pos=int(sys.argv[3])
g=next((g for g in data['gaps'] if g['id']==task),None)
if not g or g['shards']!=19 or f'FIRSTJ={pos})' not in g['shard_spec'].splitlines()[pos] or any(g['id']==task for g in data['checked']):
    sys.exit('The live desk no longer lists this task and position rule; stop.')
print(task,g['shard_spec'].splitlines()[pos])
CHECK
solver="$RUNNER_TEMP/solver/usr/bin/cadical"
sha256sum research/search13.py
python3 research/search13.py --position "$position" --cadical "$solver" --timeout 3600 --cnf "$dir/search.cnf" --proof "$dir/search.drat" --witness "$dir/witness.json" | tee "$dir/log"
sha256sum "$dir/search.cnf"
if grep -Fxq UNSAT "$dir/log"; then
    "$RUNNER_TEMP/drat-check" "$dir/search.cnf" "$dir/search.drat" > "$dir/cert.log"
    tr -d '\r' < "$dir/cert.log" | grep -Fx 's VERIFIED'
    sha256sum "$dir/search.drat"
elif test -f "$dir/witness.json"; then
    cat "$dir/witness.json"
fi
