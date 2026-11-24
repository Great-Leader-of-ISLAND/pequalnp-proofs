"""Generate finite fixed-root kernel clauses for the nine-gate subcase."""
from pathlib import Path
import sys
out=['import Bench','open CoNatBench','set_option maxHeartbeats 0','set_option maxRecDepth 5000']
for i in range(84):out.append(f'theorem c{i} : guardedSearch 8 (firstWords {i})=false := by decide +kernel')
out+=['def allFirst := (List.range 84).map firstWords','def unexpected (ws : List Word) := !(allFirst.contains ws)',
      'theorem shape : rootWords.contains target || guarded 8 unexpected rootWords = false := by decide +kernel',
      '#print axioms c83','#print axioms shape']
Path(sys.argv[1]).write_text('\n'.join(out)+'\n')
