"""One serial batch: equivalent multisets, shared fits, full audit, kernel source."""
from argparse import ArgumentParser
from pathlib import Path
from subprocess import run
import json,sys
D=Path(__file__).parent.resolve()
ap=ArgumentParser(description=__doc__)
ap.add_argument('seed0',type=Path);ap.add_argument('seed1',type=Path);ap.add_argument('outdir',type=Path)
ap.add_argument('--start',type=int,default=0);ap.add_argument('--count',type=int,default=512)
ap.add_argument('--seconds',type=int,default=30);ap.add_argument('--max-checks',type=int,default=12000)
ap.add_argument('--groups-for-kernel',type=int,default=4);ap.add_argument('--both-orientations',action='store_true')
ap.add_argument('--all-alignments',action='store_true',help='also try every genuine orientation per fixed-column key')
args=ap.parse_args()
if args.outdir.exists():ap.error('outdir exists; use a fresh directory')
args.outdir.mkdir()
for seed,source in enumerate([args.seed0,args.seed1]):
    variants=[]
    modes=([0,1] if args.both_orientations else [0])+([2] if args.all_alignments else [])
    for orbit in modes:
        out=args.outdir/f'seed{seed}-orbit{int(orbit)}.json'
        cmd=[sys.executable,str(D/'4482-share-table.py'),str(source),str(out),
             '--start',str(args.start),'--count',str(args.count),'--max-checks',str(args.max_checks),'--seconds',str(args.seconds)]
        run(cmd+(['--all-alignments'] if orbit==2 else ['--orbit'] if orbit else []),check=True)
        # Independent process rereads the actual source TSV, checks exactly
        # one membership for every original ID and replays every group.
        run([sys.executable,str(D/'4482-share-table.py'),str(source),str(out),'--audit-only'],check=True)
        doc=json.loads(out.read_text()); cost=sum(g['fuel'] for g in doc['groups'])
        variants.append((cost,len(doc['groups']),out))
    cost,n,best=min(variants)
    target=args.outdir/f'CoTightGroupRoot{seed}.lean'
    run([sys.executable,str(D/'4482-table-group-lean.py'),str(source),str(best),str(target),
         '--count',str(min(args.groups_for_kernel,n))],check=True)
    print(f'CHOSEN root={seed} rounds={cost} groups={n} manifest={best.name} lean={target.name}',flush=True)
