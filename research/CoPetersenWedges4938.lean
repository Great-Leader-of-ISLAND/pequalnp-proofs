import PEqualNP.CoRestrictedFormula4938
namespace CoFormulaMinor4938

abbrev GInput := Fin 10 → Word
abbrev I := Fin 30
def center : I → Fin 10 := ![0,0,0,1,1,1,2,2,2,3,3,3,4,4,4,5,5,5,6,6,6,7,7,7,8,8,8,9,9,9]
def left : I → Fin 10 := ![1,1,4,0,0,2,1,1,3,2,2,4,0,0,3,0,0,7,1,1,8,2,2,5,3,3,5,4,4,6]
def right : I → Fin 10 := ![4,5,5,2,6,6,3,7,7,4,8,8,3,9,9,7,8,8,8,9,9,5,9,9,5,6,6,6,7,7]
def wfam : I → Fin 4 → Nat := ![![0,4,8,104],![0,4,128,208],![0,8,128,138],![0,16,8,104],![0,16,256,276],![0,8,256,385],![0,1,16,208],![0,1,32,104],![0,16,32,50],![0,2,1,385],![0,2,32,50],![0,1,32,69],![0,2,4,548],![0,2,64,104],![0,4,64,69],![0,2,4,276],![0,2,8,138],![0,4,8,69],![0,1,8,521],![0,1,16,276],![0,8,16,50],![0,2,1,521],![0,2,16,50],![0,1,16,69],![0,4,1,69],![0,4,2,50],![0,1,2,138],![0,1,2,138],![0,1,4,69],![0,2,4,50]]

def port (i : I) (v : Fin 10) : Option (Fin 3) :=
  if v=center i then some 0 else if v=left i then some 1 else if v=right i then some 2 else none
def shapeInput (i : I) (k : Fin 4) (v : Fin 10) : Word :=
  match port i v with
  | some a => lit a
  | none => if (wfam i k).testBit v.val then 255 else 0
def wanted : Fin 4 → Word := ![168,236,248,254]
def graph (x : GInput) : Word :=
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) ||| (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) ||| (x 3 &&& x 8) ||| (x 4 &&& x 9) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 7 &&& x 9) ||| (x 8 &&& x 5) ||| (x 9 &&& x 6)

theorem witnesses (i : I) : ∀ k : Fin 4,graph (shapeInput i k)=wanted k := by
  fin_cases i <;> decide +kernel

theorem input_sound (i : I) (k : Fin 4) : ∀ v, match port i v with
    | some a => shapeInput i k v=lit a | none => shapeInput i k v=0 ∨ shapeInput i k v=255 := by
  intro v
  cases h : port i v with
  | some a => simp [shapeInput,h]
  | none => simp [shapeInput,h]; split <;> simp

theorem all_required (s : Expr) (computes : ∀ x : GInput,s.eval x=graph x) (i : I) :
    ∀ a∈required, permits (s.keep (port i)) a := by
  intro a mem
  have inlist : a ∈ List.ofFn wanted := by simpa only [required,wanted,List.ofFn_succ,List.ofFn_zero] using mem
  obtain ⟨k,hk⟩ := List.mem_ofFn.mp inlist
  have ex := restriction s (shapeInput i k) (port i) (input_sound i k)
  rwa [computes,witnesses,hk] at ex

end CoFormulaMinor4938
