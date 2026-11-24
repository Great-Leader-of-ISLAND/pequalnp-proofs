"""Replay partial signatures on all 256 input rows; keep mismatches for another pass."""
from pathlib import Path
import re,subprocess,sys,tempfile
binary=Path(sys.argv[1]).resolve()
def label(r):
    return any(r>>i & r>>j & 1 for i,j in [(0,1),(1,2),(2,3),(3,4),(0,4),(0,5),(2,6),(3,7),(5,6),(5,7)])
subprocess.run([binary,'--control'],check=True)
with tempfile.TemporaryDirectory() as d:
    rows=Path(d)/'rows'
    for neg,lo,hi in [(1,0,100000),(0,0,100000),(1,20,30)]:
        extra=[]
        for round_id in range(3):
            rows.write_text(' '.join(map(str,extra)))
            p=subprocess.run([binary,str(neg),str(lo),str(hi),'32',rows],check=True,text=True,capture_output=True)
            print(f'RUN {neg=} {lo=} {hi=} {round_id=} {extra=}',flush=True)
            print(p.stdout,flush=True)
            m=re.search(r'^FULL_REPLAY npos=\d+ nneg=\d+ mismatches=(\d+)([^\n]*)',p.stdout,re.M)
            if not m or int(m[1])==0:break
            found=[int(n) for n in m[2].split() if int(n) not in extra]
            add=[]
            for sign in [False,True]:
                add.extend([r for r in found if label(r)==sign][:2])
            assert add
            extra.extend(add)
