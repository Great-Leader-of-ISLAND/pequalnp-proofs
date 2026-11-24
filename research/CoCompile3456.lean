import PEqualNP.CoAO3143Restriction

namespace CoCompile3456
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open CoAO3143Restriction

abbrev Rows (n : Nat) := Fin n → Bool
def raw (n : Nat) : List (Wire (Rows n)) :=
  List.ofFn (fun i : Fin n => fun x : Rows n => x i)
def free (n : Nat) : List (Wire (Rows n)) := con false :: con true :: raw n
def symbolic (n : Nat) (gs : List Gate) := circuitWires gs (raw n)
def good (n : Nat) (gs : List Gate) := Monotone2 ⟨gs,0⟩ ∧ ReadsBack n ⟨gs,0⟩
def realize {n} (gs : List Gate) (pool : List (Wire (Rows n))) : Prop :=
  ∀ w∈pool, ¬ Constant w → w ∈ symbolic n gs

private theorem symLength' {α : Type} (gs : List Gate) (ws : List (Wire α)) :
    (circuitWires gs ws).length = ws.length + gs.length := by
  induction gs generalizing ws with
  | nil => simp [circuitWires]
  | cons g gs ih =>
    change (circuitWires gs (ws++[readGate ws g])).length = _
    rw [ih]
    simp <;> omega

theorem symLength (n) (gs : List Gate) : (symbolic n gs).length = n + gs.length := by
  simp [symbolic,symLength',raw]

theorem symSnoc (n) (gs : List Gate) (g : Gate) :
    symbolic n (gs++[g]) = symbolic n gs ++ [readGate (symbolic n gs) g] := by
  simp [symbolic,circuitWires,List.foldl_append]

private theorem address {α : Type} {w : α} (deflt : α) {ws : List α} (hm : w∈ws) :
    ∃ i, i<ws.length ∧ ws.getD i deflt=w := by
  induction ws with
  | nil => simp at hm
  | cons a ws ih =>
    rcases List.mem_cons.mp hm with rfl | hh
    · exact ⟨0,by simp,by simp⟩
    · obtain ⟨i,hi,hr⟩ := ih hh
      exact ⟨i+1,by simpa using hi,by simpa using hr⟩

def binary (d : Bool) (i j : Nat) : Gate := ⟨if d then .or else .and,[i,j]⟩

private theorem binaryValue {α : Type} (ws : List (Wire α)) (d : Bool) (i j : Nat) :
    readGate ws (binary d i j) = op d (ws.getD i (con false)) (ws.getD j (con false)) := by
  funext r
  cases d <;> simp [readGate,binary,op,GateOp.eval]

theorem goodSnoc {n gs} (hg : good n gs) (d : Bool) (i j : Nat)
    (hi : i<n+gs.length) (hj : j<n+gs.length) :
    good n (gs++[binary d i j]) := by
  constructor
  · intro g mem
    rcases List.mem_append.mp mem with hh | hh
    · exact hg.1 g hh
    · obtain rfl := List.mem_singleton.mp hh
      cases d <;> simp [binary]
  · intro k hk t hm
    by_cases h : k<gs.length
    · apply hg.2 k h t
      change t ∈ (gs.getD k ⟨.or,[]⟩).inputs
      change t ∈ ((gs++[binary d i j]).getD k ⟨.or,[]⟩).inputs at hm
      rwa [List.getD_append _ _ _ _ h] at hm
    · change k<(gs++[binary d i j]).length at hk
      simp only [List.length_append,List.length_cons,List.length_nil] at hk
      have he : k=gs.length := by omega
      subst k
      change t ∈ ((gs++[binary d i j]).getD gs.length ⟨.or,[]⟩).inputs at hm
      have last : (gs++[binary d i j]).getD gs.length ⟨.or,[]⟩ = binary d i j := by
        simp [List.getD_eq_getElem?_getD,List.getElem?_append]
      rw [last] at hm
      simp only [binary,List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl | rfl
      · exact hi
      · exact hj

private theorem absorb {α : Type} (a b : Wire α) (d : Bool)
    (hc : Constant a ∨ Constant b) :
    Constant (op d a b) ∨ op d a b=a ∨ op d a b=b := by
  rcases hc with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases d <;> cases v
    · exact Or.inl ⟨false,by funext i; simp [op,con]⟩
    · exact Or.inr (Or.inr (by funext i; simp [op,con]))
    · exact Or.inr (Or.inr (by funext i; simp [op,con]))
    · exact Or.inl ⟨true,by funext i; simp [op,con]⟩
  · cases d <;> cases v
    · exact Or.inl ⟨false,by funext i; simp [op,con]⟩
    · exact Or.inr (Or.inl (by funext i; simp [op,con]))
    · exact Or.inr (Or.inl (by funext i; simp [op,con]))
    · exact Or.inl ⟨true,by funext i; simp [op,con]⟩

theorem compilePool {n k} {pool : List (Wire (Rows n))} (h : Build (free n) k pool) :
    ∃ gs : List Gate, gs.length ≤ k ∧ good n gs ∧ realize gs pool := by
  classical
  induction h with
  | start =>
    refine ⟨[],by simp,?_,?_⟩
    · exact ⟨fun _ h => by simp at h,fun _ h => by simp at h⟩
    · intro w hw hn
      change w ∈ con false::con true::raw n at hw
      rcases List.mem_cons.mp hw with rfl | hh
      · exact (hn ⟨false,rfl⟩).elim
      rcases List.mem_cons.mp hh with rfl | hh
      · exact (hn ⟨true,rfl⟩).elim
      · exact hh
  | @gate k pool pre d a b ha hb ih =>
    obtain ⟨gs,hsize,hgood,present⟩ := ih
    by_cases hc : Constant a ∨ Constant b
    · refine ⟨gs,by omega,hgood,?_⟩
      intro w hw hn
      rcases List.mem_cons.mp hw with rfl | old
      · rcases absorb a b d hc with hc | eq | eq
        · exact (hn hc).elim
        · rw [eq] at hn ⊢; exact present a ha hn
        · rw [eq] at hn ⊢; exact present b hb hn
      · exact present w old hn
    · obtain ⟨i,hi,ai⟩ := address (con false) (present a ha (fun h => hc (Or.inl h)))
      obtain ⟨j,hj,bj⟩ := address (con false) (present b hb (fun h => hc (Or.inr h)))
      rw [symLength] at hi hj
      refine ⟨gs++[binary d i j],by simpa using hsize,goodSnoc hgood d i j hi hj,?_⟩
      intro w hw hn
      rw [symSnoc]
      rcases List.mem_cons.mp hw with rfl | old
      · apply List.mem_append_right
        apply List.mem_singleton.mpr
        rw [binaryValue,ai,bj]
      · exact List.mem_append_left _ (present w old hn)

theorem compile {n k} {pool : List (Wire (Rows n))} {out : Wire (Rows n)}
    (h : Build (free n) k pool) (ho : out∈pool) (hn : ¬Constant out) :
    ∃ C : Circuit, Monotone2 C ∧ ReadsBack n C ∧ C.size ≤ k ∧ circuitFun n C = out := by
  obtain ⟨gs,budget,hgood,present⟩ := compilePool h
  obtain ⟨i,_,hw⟩ := address (con false) (present out ho hn)
  refine ⟨⟨gs,i⟩,hgood.1,hgood.2,budget,?_⟩
  funext r
  have ev := circuit_rows gs (raw n) r
  have inps : (raw n).map (fun w => w r) = List.ofFn r := by
    simp only [raw,List.map_ofFn] <;> rfl
  rw [inps] at ev
  change ((⟨gs,i⟩ : Circuit).wires (List.ofFn r)).getD i false = out r
  change (symbolic n gs).map (fun w => w r) = (⟨gs,i⟩ : Circuit).wires (List.ofFn r) at ev
  rw [←ev]
  have read :
      ((symbolic n gs).map (fun w => w r)).getD i false =
      (symbolic n gs).getD i (con false) r := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases (symbolic n gs)[i]? <;> rfl
  rw [read]
  exact congrFun hw r

end CoCompile3456
