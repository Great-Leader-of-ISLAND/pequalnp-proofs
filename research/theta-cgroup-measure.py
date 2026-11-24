"""Run one already confined Lean command, report actual cgroup peak and GNU process peak separately."""
from pathlib import Path
import os,subprocess,sys
group=next(x.split(':',2)[2] for x in Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0::'))
cg=Path('/sys/fs/cgroup')/group.lstrip('/')
def read(name):return (cg/name).read_text().strip()
configured=int(read('memory.max'));page=os.sysconf('SC_PAGE_SIZE')
assert 6500000000-page < configured <= 6500000000 and read('memory.swap.max')=='0',(group,configured)
print('actual cgroup:',group,'memory.max',read('memory.max'),'memory.swap.max',read('memory.swap.max'),flush=True)
cmd=['/usr/bin/time','-v','/usr/bin/timeout','1200',*sys.argv[1:]]
r=subprocess.run(cmd)
print('actual cgroup memory.peak bytes:',read('memory.peak'),'memory.events:',read('memory.events').replace('\n',' '),flush=True)
sys.exit(r.returncode if r.returncode>=0 else 128-r.returncode)
