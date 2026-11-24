"""Replace only the complete-cover test on the two-dropped-operands branch."""
from pathlib import Path
import sys
def fast(s):
  k=s.index('def guarded (')
  e=s.index('def guardedSearch',k)
  original=s[k:e]
  assert 'let once := bucket.1 ^^^ bucket.2' in original
  t=original.replace('let bucket := multiplicities ws','let bucket := threeCounts ws').replace('bucket.1 ^^^ bucket.2','bucket.1 ^^^ bucket.2.1')
  t=t.replace('  let cols :=','  let doubleMask := bucket.2.1 ^^^ bucket.2.2\n  let cols :=').replace('let base := cover rest','let lost := (sep a.1 &&& sep b.1) &&& doubleMask')
  t=t.replace('(base ||| sep z)==all','(lost &&& sep z)==lost').replace('(base ||| sep z) == all','(lost &&& sep z) == lost')
  assert 'base |||' not in t and 'lost &&& sep z' in t
  m="""def threeCounts : List Word → Nat × (Nat × Nat)
  | [] => (0,0,0)
  | w::ws =>
    let d := sep w
    let c := threeCounts ws
    (d ||| c.1,(d &&& c.1) ||| c.2.1,(d &&& c.2.1) ||| c.2.2)

"""
  return s[:k]+m+t+s[e:]
if __name__=='__main__':
  p=Path(sys.argv[1]);p.write_text(fast(p.read_text()))
