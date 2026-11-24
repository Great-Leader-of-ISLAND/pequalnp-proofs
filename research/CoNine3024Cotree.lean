import PEqualNP.CoAO3143Restriction

namespace CoNine3024Cotree
open CoAO3143Restriction

noncomputable section
local instance {α : Type} : DecidableEq (Wire α) := Classical.decEq _

def sep {α : Type} (p n : α) (w : Wire α) : Prop := w p=true ∧ w n=false

def pairRule {α : Type} (f : α→α→Wire α) : Prop :=
  ∀ p n₁ n₂ p₁ p₂ n, f p n₁=f p₁ n → f p n₂=f p₂ n → f p n₁=f p n₂

def routing {α : Type} (out : Wire α) (S : Finset (Wire α)) : Prop :=
  ∃ f : α→α→Wire α, pairRule f ∧
    ∀ p n, f p n∈S ∧ (sep p n out → sep p n (f p n))

private def pick {α : Type} (d : Bool) (a b : Wire α) (p n : α) :=
  if d then (if a p then a else b) else (if a n then b else a)

private theorem pick_mem {α : Type} (d : Bool) (a b : Wire α) (p n : α) :
    pick d a b p n=a ∨ pick d a b p n=b := by
  cases d <;> cases e : a p <;> cases v : a n <;> simp [pick,e,v]

private theorem pick_sep {α : Type} (d : Bool) (a b : Wire α) (p n : α)
    (h : sep p n (op d a b)) : sep p n (pick d a b p n) := by
  cases d <;> cases e : a p <;> cases v : a n <;> simp_all [pick,sep,op]

/-- Expand a leaf into a gate. Tight width ensures its two operand labels are
absent from all remaining live labels, so the old route can be recovered. -/
private theorem splice {α : Type} {out : Wire α} (U : Finset (Wire α))
    (d : Bool) (a b : Wire α) (ha : a∉U) (hb : b∉U)
    (old : routing out (insert (op d a b) U)) : routing out (insert a (insert b U)) := by
  obtain ⟨f,rule,valid⟩ := old
  let z := op d a b
  let next := fun p n => if f p n=z then pick d a b p n else f p n
  let parent := fun w : Wire α => if w=a ∨ w=b then z else w
  have outside (p n) (h : f p n≠z) : f p n∈U :=
    (Finset.mem_insert.mp (valid p n).1).resolve_left h
  have back (p n) : parent (next p n)=f p n := by
    by_cases h : f p n=z
    · simp [next,h,parent,pick_mem]
    · have hu := outside p n h
      have ea : f p n≠a := fun e => ha (e ▸ hu)
      have eb : f p n≠b := fun e => hb (e ▸ hu)
      simp [next,h,parent,ea,eb]
  refine ⟨next,?_,?_⟩
  · intro p n₁ n₂ p₁ p₂ n e₁ e₂
    have f₁ := congrArg parent e₁
    have f₂ := congrArg parent e₂
    rw [back,back] at f₁ f₂
    have shared := rule p n₁ n₂ p₁ p₂ n f₁ f₂
    by_cases z₁ : f p n₁=z
    · have z₂ := shared.symm.trans z₁
      have z₃ := f₁.symm.trans z₁
      have z₄ := f₂.symm.trans z₂
      simp only [next,z₁,z₂,z₃,z₄,if_true] at e₁ e₂ ⊢
      cases d
      · exact e₁.trans e₂.symm
      · rfl
    · have z₂ : f p n₂≠z := fun h => z₁ (shared.trans h)
      simpa only [next,z₁,z₂,if_false] using shared
  · intro p n
    by_cases h : f p n=z
    · simp only [next,h,if_true]
      refine ⟨?_,?_⟩
      · rcases pick_mem d a b p n with l|r <;> simp [*]
      · intro yes
        have sepZ := (valid p n).2 yes
        rw [h] at sepZ
        exact pick_sep d a b p n sepZ
    · simp only [next,h,if_false]
      exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (outside p n h)),(valid p n).2⟩

private theorem width {α : Type} {out : Wire α} {k S} (c : Cone out k S) : S.card≤k+1 := by
  induction c with
  | stop => simp
  | @gate k U d a b fresh tail ih =>
    rw [Finset.card_insert_of_notMem fresh] at ih
    have x := Finset.card_insert_le a (insert b U)
    have y := Finset.card_insert_le b U
    omega

theorem tight_route {α : Type} {out : Wire α} {k S} (c : Cone out k S)
    (tight : S.card=k+1) : routing out S := by
  induction c with
  | stop => exact ⟨fun _ _ => out,fun _ _ _ _ _ _ _ _ => rfl,fun _ _ => ⟨by simp,id⟩⟩
  | @gate k U d a b fresh tail ih =>
    have bound := width tail
    rw [Finset.card_insert_of_notMem fresh] at bound
    have ha : a∉insert b U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight
      have eq := Finset.card_insert_le b U
      omega
    rw [Finset.card_insert_of_notMem ha] at tight
    have hb : b∉U := by intro h; rw [Finset.insert_eq_of_mem h] at tight; omega
    rw [Finset.card_insert_of_notMem hb] at tight
    apply splice U d a b (fun x => ha (Finset.mem_insert_of_mem x)) hb
    apply ih
    rw [Finset.card_insert_of_notMem fresh]
    omega

def Forced {α : Type} (S : Finset (Wire α)) (p n : α) (a : Wire α) : Prop :=
  ∀ w∈S, sep p n w → w=a

/-- On the full domain of the physical Cone, a single pair of distinct
forced sources cannot be seen both along a fixed positive row and along a
fixed negative row at tight width. The four cells need not form a rectangle. -/
theorem forced_pair {α : Type} {out : Wire α} {k S} (c : Cone out k S)
    (tight : S.card=k+1) {p p₁ p₂ n n₁ n₂ : α} {a b : Wire α}
    (t₁ : sep p n₁ out) (t₂ : sep p n₂ out) (t₃ : sep p₁ n out) (t₄ : sep p₂ n out)
    (a₁ : Forced S p n₁ a) (b₁ : Forced S p n₂ b)
    (a₂ : Forced S p₁ n a) (b₂ : Forced S p₂ n b) : a=b := by
  obtain ⟨f,rule,valid⟩ := tight_route c tight
  have leaf {i j w} (test : sep i j out) (h : Forced S i j w) : f i j=w :=
    h _ (valid i j).1 ((valid i j).2 test)
  have s₁ := leaf t₁ a₁
  have s₂ := leaf t₂ b₁
  exact (s₁.symm.trans (rule p n₁ n₂ p₁ p₂ n
    (s₁.trans (leaf t₃ a₂).symm) (s₂.trans (leaf t₄ b₂).symm))).trans s₂

#print axioms forced_pair
end
end CoNine3024Cotree
