import PEqualNP.CoMask3024
namespace CoTwo2590
open CoAO3143Restriction
abbrev Row := Fin 1024
def x (i : Fin 10) (r : Row) : Bool := r.val.testBit i.val
def F (r : Row) : Bool := (x 0 r && x 1 r) || (x 0 r && x 4 r) || (x 0 r && x 5 r) || (x 1 r && x 2 r) || (x 1 r && x 6 r) || (x 2 r && x 3 r) || (x 2 r && x 7 r) || (x 3 r && x 4 r) || (x 3 r && x 8 r) || (x 4 r && x 9 r) || (x 5 r && x 7 r) || (x 5 r && x 8 r) || (x 6 r && x 8 r) || (x 6 r && x 9 r) || (x 7 r && x 9 r)
def z : Wire Row := op false (x 0) (x 2)
def bank (j : Fin 11) : Wire Row := if h : j.val<10 then x ⟨j.val,h⟩ else z
def wire (a b : Fin 11) (d : Bool) : Wire Row := op d (bank a) (bank b)
def other (p : Fin 10) (a b : Fin 11) : Nat :=
  if a.val=p.val then b.val else if b.val=p.val then a.val else 11
def index (p : Fin 10) (a b : Fin 11) (d : Bool) : Fin 240 :=
  ⟨((p.val*12+other p a b)*2+d.toNat)%240,Nat.mod_lt _ (by decide)⟩
def yesTable : Fin 240 → Row := ![0,0,17,3,3,17,3,3,3,3,3,3,3,17,3,3,3,3,3,3,3,0,3,3,6,3,0,0,3,3,3,3,3,6,3,6,3,3,3,3,3,3,3,3,3,3,3,3,6,12,12,6,0,0,6,6,6,6,6,6,6,12,6,6,6,6,6,6,6,0,6,6,12,12,12,24,24,12,0,0,12,12,12,12,12,12,12,24,12,12,12,12,12,12,12,12,24,17,17,24,17,17,17,17,0,0,17,24,17,17,17,17,17,17,17,17,17,17,17,17,160,33,33,160,33,33,33,33,33,160,0,0,33,33,33,33,33,33,33,33,33,33,33,33,66,320,320,66,66,320,66,66,66,66,66,66,0,0,66,66,66,66,66,66,66,320,66,66,132,132,132,160,160,132,132,160,132,132,132,132,132,132,0,0,132,132,132,132,132,132,132,132,264,264,264,264,264,288,288,264,264,288,264,264,264,264,264,264,0,0,264,264,264,320,264,264,528,576,528,528,528,528,528,576,576,528,528,528,528,528,528,528,528,528,0,0,528,576,528,528]
def noTable : Fin 240 → Row := ![0,0,50,50,50,116,50,138,50,50,50,50,50,116,50,138,50,402,50,554,50,0,50,50,69,69,0,0,69,69,69,201,69,116,69,116,69,69,69,201,69,385,69,521,69,69,69,69,50,201,104,50,0,0,50,138,50,50,50,50,50,104,50,138,50,402,50,554,50,0,50,50,69,69,69,50,50,69,0,0,69,116,69,116,69,69,69,208,69,276,69,548,69,69,69,69,104,69,69,138,69,69,69,201,0,0,69,104,69,69,69,201,69,385,69,521,69,69,69,69,138,69,69,138,69,69,69,201,69,208,0,0,69,69,69,201,69,385,69,521,69,69,69,69,50,385,276,50,50,276,50,138,50,50,50,50,0,0,50,138,50,402,50,554,50,773,50,50,69,69,69,50,50,69,69,104,69,116,69,116,69,69,0,0,69,276,69,548,69,69,69,69,104,201,104,138,104,116,50,104,104,50,104,104,104,104,104,138,0,0,104,521,104,69,104,104,50,69,50,50,50,116,50,104,69,50,50,50,50,116,50,208,50,276,0,0,50,69,50,50]
def yes (p : Fin 10) (a b : Fin 11) (d : Bool) := yesTable (index p a b d)
def no (p : Fin 10) (a b : Fin 11) (d : Bool) := noTable (index p a b d)
def isAlias (p : Fin 10) (a b : Fin 11) (d : Bool) : Bool :=
  (a.val==p.val && b.val==p.val) ||
  (d && (p.val==0 || p.val==2) && ((a.val==p.val && b.val==10) || (b.val==p.val && a.val==10)))

private theorem alias_value (p : Fin 10) (a b : Fin 11) (d : Bool)
    (h : isAlias p a b d=true) : wire a b d=x p := by
  funext r
  simp only [isAlias,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at h
  have read (i : Fin 11) (eq : i.val=p.val) : bank i=x p := by
    have lt : i.val<10 := eq ▸ p.isLt
    simp only [bank,dif_pos lt]
    exact congrArg x (Fin.ext eq)
  rcases h with ⟨ap,bp⟩|⟨⟨dt,hp⟩,alt⟩
  · cases d <;> simp [wire,op,read a ap,read b bp]
  · subst d
    have last (i : Fin 11) (eq : i.val=10) : bank i=z := by simp [bank,eq]
    rcases alt with ⟨ap,bz⟩|⟨bp,az⟩ <;> rcases hp with e|e
    all_goals
      first | rw [wire,read a ap,last b bz] | rw [wire,last a az,read b bp]
      have ix : p=0 ∨ p=2 := by first | exact Or.inl (Fin.ext e) | exact Or.inr (Fin.ext e)
      rcases ix with rfl|rfl <;> dsimp only [z,op] <;> cases x 0 r <;> cases x 2 r <;> rfl

def separation (p : Fin 10) (a b : Fin 11) (d : Bool) : Prop :=
  let high := yes p a b d
  let low := no p a b d
  F high=true ∧ F low=false ∧ (z high=true → z low=true) ∧
  (wire a b d high=true → wire a b d low=true) ∧
  ∀ i : Fin 10,i≠p → x i high=true → x i low=true

instance (p : Fin 10) (a b : Fin 11) (d : Bool) : Decidable (separation p a b d) := by
  unfold separation; infer_instance

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem sep0 : ∀ (a b : Fin 11) (d : Bool), isAlias 0 a b d=false → separation 0 a b d := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem sep1 : ∀ (a b : Fin 11) (d : Bool), isAlias 1 a b d=false → separation 1 a b d := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem sep2 : ∀ (a b : Fin 11) (d : Bool), isAlias 2 a b d=false → separation 2 a b d := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem sep3 : ∀ (a b : Fin 11) (d : Bool), isAlias 3 a b d=false → separation 3 a b d := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem sep4 : ∀ (a b : Fin 11) (d : Bool), isAlias 4 a b d=false → separation 4 a b d := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem sep5 : ∀ (a b : Fin 11) (d : Bool), isAlias 5 a b d=false → separation 5 a b d := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem sep6 : ∀ (a b : Fin 11) (d : Bool), isAlias 6 a b d=false → separation 6 a b d := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem sep7 : ∀ (a b : Fin 11) (d : Bool), isAlias 7 a b d=false → separation 7 a b d := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem sep8 : ∀ (a b : Fin 11) (d : Bool), isAlias 8 a b d=false → separation 8 a b d := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem sep9 : ∀ (a b : Fin 11) (d : Bool), isAlias 9 a b d=false → separation 9 a b d := by decide +kernel

/-- In any live monotone suffix after AND(0,2) and a second physical binary gate,
    every raw coordinate remains necessary unless the second output itself is its copy. -/
theorem all_ten (a b : Fin 11) (d : Bool) {k S} (c : Cone F k S)
    (sources : ∀ w∈S,(∃i : Fin 10,w=x i) ∨ w=z ∨ w=wire a b d)
    (present : wire a b d∈S) (p : Fin 10) : x p∈S := by
  classical
  by_cases copied : isAlias p a b d=true
  · exact alias_value p a b d copied ▸ present
  have sep : separation p a b d := by
    have zero := Bool.eq_false_iff.mpr copied
    fin_cases p
    · exact sep0 a b d zero
    · exact sep1 a b d zero
    · exact sep2 a b d zero
    · exact sep3 a b d zero
    · exact sep4 a b d zero
    · exact sep5 a b d zero
    · exact sep6 a b d zero
    · exact sep7 a b d zero
    · exact sep8 a b d zero
    · exact sep9 a b d zero

  obtain ⟨hi,lo,sz,sw,sr⟩ := sep
  by_contra absent
  have bad := CoMask3024.ordered c (yes p a b d) (no p a b d) (by
    intro w hw hit
    rcases sources w hw with ⟨i,rfl⟩|rfl|rfl
    · exact sr i (fun e => absent (e ▸ hw)) hit
    · exact sz hit
    · exact sw hit) hi
  exact Bool.false_ne_true (lo.symm.trans bad)

#print axioms CoTwo2590.all_ten
end CoTwo2590
