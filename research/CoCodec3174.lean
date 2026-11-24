import PEqualNP.CoNine3024CanonCodec

namespace CoCodec3174
open CoNine3024 CoNine3024.Canon
def initial (i : Nat) : Truth :=
  if h : i<9 then rawTruth ⟨i,h⟩ else ~~~rawTruth 0

def column (rootCount base : Nat) (recipes : Packed) : Nat → Nat → Truth
  | 0,i => initial i
  | n+1,i =>
    if i<rootCount then initial i else
      let entry := recipes.read (i-rootCount)
      let a := column rootCount base recipes n (entry%base)
      let b := column rootCount base recipes n ((entry/base)%base)
      if entry/(base*base)=0 then a &&& b else a ||| b

def labelWord (rootCount base maxdepth ybase nbase : Nat) (recipes desc : Packed)
    (t : Array Nat) (stride rf period : Nat) (i : Nat) : Atom :=
  let w := desc.read i
  let y := w/base
  let n := y/ybase
  let f := n/nbase
  let grid : Array Nat := #[0,1,32,33,1024,1025,1056,1057,32768,32769,32800,32801,33792,33793,33824,33825]
  expand t stride rf period (column rootCount base recipes maxdepth (w%base))
    (y%ybase) (n%nbase) (scatter grid 20 3 f)

end CoCodec3174
