import PEqualNP.CoPortCut4482

namespace CoPortRoots4482
open CoPortBank4482 CoPortCut4482 CoPortTrace4482 PEqualNP.CircuitLowerBounds

abbrev W := BitVec 512
abbrev R := Fin 512
abbrev Input := Fin 9 → Bool

def raw : Fin 9 → W := ![
  0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
  0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
  0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
  0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
  0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
  0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
  0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
  0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def seed : W := raw 0 ||| raw 2
def raws : List W := List.ofFn raw
def init : List W := raws++[seed]
def top : W := BitVec.allOnes 512
def roots : Finset W := insert 0 (insert top init.toFinset)
def cell (w : W) (r : R) := w.getLsbD r.val
def row (r : R) : Input := fun j => cell (raw j) r
def graph (x : Input) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any fun e =>
  x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e%10))
def label (r : R) := graph (row r)

def join (d : Bool) (a b : W) : W := if d then a ||| b else a &&& b

def model : Model W R where
  zero := 0
  one := top
  join := join
  val := cell
  atZero := by intro r; simp [cell]
  atOne := by intro r; simp only [cell,top,BitVec.getLsbD_allOnes,r.isLt,decide_true]
  applyJoin := by intro d a b r; cases d <;> simp [join,cell,BitVec.getLsbD_or,BitVec.getLsbD_and]

def lo : Fin 9 → R := ![20,1,9,4,1,1,2,4,8]
def hi : Fin 9 → R := ![21,3,13,12,17,33,66,132,264]

private theorem critical : ∀ i : Fin 9, label (lo i) ≠ label (hi i) ∧
    ((0::top::init).all fun w => w==raw i || cell w (lo i)==cell w (hi i))=true := by
  decide +kernel

private theorem necessary {A : Finset W} (sub : A⊆roots) (d : Distinguishes cell label A) :
    raws.toFinset ⊆ A := by
  intro w hw
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hw)
  obtain ⟨z,hz,ne⟩ := d _ _ (critical j).1
  have mem : z∈0::top::init := by
    simpa only [roots,Finset.mem_insert,List.mem_toFinset,List.mem_cons] using sub hz
  have or := List.all_eq_true.mp (critical j).2 z mem
  simp only [Bool.or_eq_true] at or
  rcases or with eq|bad
  · exact (beq_iff_eq.mp eq) ▸ hz
  · exact (ne (beq_iff_eq.mp bad)).elim

theorem only_roots {k A} (sub : A⊆roots) (path : Path join (cleanCut model label 6) k A) :
    A=raws.toFinset ∨ A=init.toFinset := by
  have d := separated cell label model.applyJoin (fun _ h => h.2.1) path
  have lower := necessary sub d
  have z : (0 : W)∉A := avoid (c:=(0:W)) (by
    intro d a b eq
    rcases eq with rfl|rfl <;> cases d <;> simp [join]) (fun _ h => h.2.2.1) path
  have o : top∉A := avoid (c:=top) (by
    intro d a b eq
    rcases eq with rfl|rfl <;> cases d
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [join,Bool.false_eq_true,↓reduceIte,ite_false,top,BitVec.getLsbD_and,BitVec.getLsbD_allOnes,hi,decide_true,Bool.true_and]
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [join,ite_true,top,BitVec.getLsbD_or,BitVec.getLsbD_allOnes,hi,decide_true,Bool.true_or]
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [join,Bool.false_eq_true,↓reduceIte,ite_false,top,BitVec.getLsbD_and,BitVec.getLsbD_allOnes,hi,decide_true,Bool.and_true]
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [join,ite_true,top,BitVec.getLsbD_or,BitVec.getLsbD_allOnes,hi,decide_true,Bool.or_true]) (fun _ h => h.2.2.2) path
  have upper : A⊆init.toFinset := by
    intro a ha
    rcases Finset.mem_insert.mp (sub ha) with rfl|rest
    · exact (z ha).elim
    rcases Finset.mem_insert.mp rest with rfl|h
    · exact (o ha).elim
    · exact h
  by_cases keep : seed∈A
  · right
    apply Finset.Subset.antisymm upper
    intro w hw
    rcases List.mem_append.mp (List.mem_toFinset.mp hw) with r|s
    · exact lower (List.mem_toFinset.mpr r)
    · exact (List.mem_singleton.mp s).symm ▸ keep
  · left
    apply Finset.Subset.antisymm _ lower
    intro w hw
    rcases List.mem_append.mp (List.mem_toFinset.mp (upper hw)) with r|s
    · exact List.mem_toFinset.mpr r
    · exact (keep (List.mem_singleton.mp s ▸ hw)).elim

end CoPortRoots4482
