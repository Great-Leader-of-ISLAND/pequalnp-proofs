"""Split exact computational declarations into one shared module in disposable CI workspace."""
from pathlib import Path
import argparse
import re

a = argparse.ArgumentParser()
a.add_argument('project',type=Path)
project = a.parse_args().project
library = project / 'PEqualNP'
names = {
    'Raw': 'Pin Sig missing',
    'Dimacs': 'SignedVar eraseConstant asInteger',
    'Numbered': 'Field gateFields finalFields staticNames slot rowBase address',
    'Formula': ('CNF Col pos neg constLit allFin cumFour cumLines bit op pin pref fp fq opLines '
                'structureLines muxLines truthLines wire operand cell gateRow lastRow Parts emit '
                'body ground seed xs head edges target labels columns raw35 dimacs35')
}
names = {
    'Raw': 'Pin Sig missing',
    'Dimacs': 'SignedVar eraseConstant asInteger',
    'Numbered': 'Field',
    'Formula': 'CNF Col pos neg constLit allFin cumFour cumLines muxLines truthLines wire Parts seed xs head edges target labels columns',
    'Fast': 'gateBase supported staticCalc fastAddress fbit fop fpin fpre ffp ffq fcell fopLines fstatic foperand fgateRow flastRow femit'
}
unified = ['import Mathlib.Data.Fin.VecNotation\n', 'import Mathlib.Data.List.FinRange\n']
for unit, selected in names.items():
    path = library / f'CoPetersen{unit}.lean'
    namespace = f'PEqualNP.Research.Petersen{unit}'
    unified.append(f'\nnamespace {namespace}\n')
    if unit in ('Formula', 'Fast'):
        unified.extend('open PEqualNP.Research.Petersen'+other+'\n' for other in (['Raw','Dimacs','Numbered'] + (['Formula'] if unit == 'Fast' else [])))
    lines = path.read_text().splitlines(keepends=True)
    selected = set(selected.split())
    others = ['import PEqualNP.CoPetersenExecDefs\n']
    i = 0
    while i < len(lines):
        m = re.match(r'(?:def|abbrev|structure|inductive) (\w+)', lines[i])
        if m is None or m[1] not in selected:
            others.append(lines[i])
            i += 1
            continue
        selected.remove(m[1])
        j = i + 1
        while j < len(lines) and lines[j].startswith((' ', '\t')):
            j += 1
        unified.append('\n')
        unified.extend(lines[i:j])
        i = j
    assert not selected, selected
    path.write_text(''.join(others))
    if unit == 'Fast':
        raw = path.read_text()
        begin = raw.index('def fastDimacs35 :')
        end = raw.index('\ntheorem fastDimacs35_eq',begin)
        expr = raw[begin:end].replace('def fastDimacs35 :','def dynamicDimacs (k : ℕ) :').replace('femit 14 0 columns labels','femit k 0 columns labels')
        assert 'dynamicDimacs' in expr and 'femit k 0 columns labels' in expr
        unified.append('\n'+expr+'\n')
        witness = 'theorem dynamic14_exact : dynamicDimacs 14 = dimacs35 := fastDimacs35_eq\n\n'
        path.write_text(raw.replace('end '+namespace, witness + 'end '+namespace))
    unified.append(f'\nend {namespace}\n')
(library/'CoPetersenExecDefs.lean').write_text(''.join(unified))
