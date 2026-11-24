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
unified = ['import Mathlib.Data.Fin.VecNotation\n', 'import Mathlib.Data.List.FinRange\n']
for unit, selected in names.items():
    path = library / f'CoPetersen{unit}.lean'
    namespace = f'PEqualNP.Research.Petersen{unit}'
    unified.append(f'\nnamespace {namespace}\n')
    if unit == 'Formula':
        unified.extend('open PEqualNP.Research.Petersen'+other+'\n' for other in ['Raw','Dimacs','Numbered'])
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
    unified.append(f'\nend {namespace}\n')
(library/'CoPetersenExecDefs.lean').write_text(''.join(unified))
