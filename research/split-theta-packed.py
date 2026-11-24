#!/usr/bin/env python3
"""Separate large batches of ground kernel decisions from the final theorem.
All chunks import the same packed definitions. Generated sources are sufficient
to reconstruct the theorem without a precompiled object or a trusted oracle.
"""
import argparse
from pathlib import Path

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('source',type=Path);p.add_argument('outdir',type=Path)
p.add_argument('--spans',type=int,default=8,help='Number of finite span decisions per importable module.')
opt=p.parse_args()
if opt.spans < 1:raise ValueError('positive spans required')
src=opt.source.read_text().splitlines();folder=opt.outdir;folder.mkdir(parents=True,exist_ok=True)
opening='namespace CoThetaWholeBase.CertifiedData'
end='end CoThetaWholeBase.CertifiedData'
data=[];blocks=[];final=[];piece=[];mode='base';levels=[]
for line in src:
    if line==end:continue
    if line.startswith('def pass'):
        mode='proofs'
        data.append(line);levels.append(int(line.split('pass',1)[1].split(' ',1)[0]));continue
    if mode=='base':
        data.append(line)
    elif line.startswith('private theorem blk_'):
        blocks.append(line.replace('private theorem','theorem',1))
    else:final.append(line)
assert levels and blocks
(folder/'CoThetaPackedData.lean').write_text('\n'.join([*data,end])+'\n')
prefix=['import PEqualNP.CoThetaPackedData',opening,'open PEqualNP.CircuitLowerBounds','set_option maxRecDepth 30000','set_option maxHeartbeats 0']
names=[]
for j in range(0,len(blocks),opt.spans):
    name=f'CoThetaBlock{len(names):03}';names.append(name)
    (folder/f'{name}.lean').write_text('\n'.join([*prefix,*blocks[j:j+opt.spans],end])+'\n')
exports=[f'import PEqualNP.{n}' for n in names]
(folder/'CoThetaPackedFinal.lean').write_text('\n'.join([*exports,*prefix[1:],*final,end])+'\n')
diag=['def rejection (k t i : Nat) : Bool :=']
for k in sorted(levels):
    diag.append(f'  if k={k} then pass{k} t i else')
diag+=['  false','def counts (k t : Nat) : Nat :=']
for k in sorted(levels):diag.append(f'  if k={k} then count{k} t else')
diag+=['  0','def diagnostic : IO Unit := do','  for k in '+str(list(sorted(levels)))+' do',
       '    let mut examined := 0','    let mut failed := 0','    for t in List.range 8 do',
       '      for i in List.range (counts k t) do','        examined := examined + 1',
       '        if !rejection k t i then','          failed := failed + 1',
       '          if failed ≤ 3 then IO.println s!"rejected-data k={k} t={t} i={i}"',
       '    IO.println s!"executable cross-check k={k} examined={examined} failed={failed}"',
       '    if failed > 0 then throw (IO.userError "untrusted trace mismatch")',end,
       'def main : IO Unit := CoThetaWholeBase.CertifiedData.diagnostic']
(folder/'CoThetaPackedDiagnostic.lean').write_text('\n'.join([*prefix,*diag])+'\n')
print('partitioned',len(blocks),'kernel spans into',len(names),'modules, stages',levels)
