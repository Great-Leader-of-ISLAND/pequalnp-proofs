import PEqualNP.CoDominance2590
import PEqualNP.CoAO3143Restriction

namespace CoDominanceLoss2590
open CoAO3143Restriction
noncomputable section
local instance {α : Type} : DecidableEq (Wire α) := Classical.decEq _
local instance (p : Prop) : Decidable p := Classical.propDecidable _

def count {X : Type} (P : X → Prop) (S : Finset X) := (@Finset.filter X P (fun _ => Classical.propDecidable _) S).card

private theorem charge {X : Type} [DecidableEq X] {P Q : X → Prop} {U : Finset X} {a b z : X}
    (fresh : z∉U) (agree : ∀ w∈U,P w ↔ Q w) (both : P a → P b → Q z) :
    (if P a ∨ P b then 0 else 1) + count P (insert a (insert b U)) ≤ 1+count Q (insert z U) := by
  classical
  have left (w : X) (s : Finset X) : count P (insert w s) ≤ count P s + (if P w then 1 else 0) := by
    unfold count
    rw [Finset.filter_insert]
    by_cases h : P w
    · simp only [h,if_true]
      exact Finset.card_insert_le _ _
    · simp [h]
  have congr : count P U=count Q U := by
    unfold count
    congr 1
    ext w
    by_cases h : w∈U
    · simp [h,agree w h]
    · simp [h]
  have right : count Q (insert z U) = count Q U + (if Q z then 1 else 0) := by
    unfold count
    rw [Finset.filter_insert]
    by_cases h : Q z
    · have nz : z∉U.filter Q := fun w => fresh (Finset.mem_filter.mp w).1
      simp only [h,if_true]
      exact Finset.card_insert_of_notMem nz
    · simp [h]
  have ax := left a (insert b U)
  have bx := left b U
  rw [right,←congr]
  by_cases ha : P a <;> by_cases hb : P b
  · have hz := both ha hb
    simp [ha,hb,hz] at ax bx ⊢
    omega
  all_goals by_cases hz : Q z <;> simp [ha,hb,hz] at ax bx ⊢ <;> omega

private theorem output_form {β : Type} (a b : Wire β) (d : Bool)
    (h : Constant a ∨ Constant b) :
      (∃ v, op d a b = con v) ∨ op d a b=a ∨ op d a b=b := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases d <;> cases v
    · exact Or.inl ⟨false, by funext i; simp [op,con]⟩
    · exact Or.inr (Or.inr (by funext i; simp [op,con]))
    · exact Or.inr (Or.inr (by funext i; simp [op,con]))
    · exact Or.inl ⟨true, by funext i; simp [op,con]⟩
  · cases d <;> cases v
    · exact Or.inl ⟨false, by funext i; simp [op,con]⟩
    · exact Or.inr (Or.inl (by funext i; simp [op,con]))
    · exact Or.inr (Or.inl (by funext i; simp [op,con]))
    · exact Or.inl ⟨true, by funext i; simp [op,con]⟩

private theorem cheap {β : Type} {xs : List (Wire β)} (cs : ∀ i : Bool,con i∈xs)
    (d : Bool) {a b : Wire β} (ha : a∈xs) (hb : b∈xs) (h : Constant a ∨ Constant b) :
    op d a b∈xs := by
  rcases output_form a b d h with ⟨v,e⟩|e|e
  · rw [e]; exact cs v
  · rw [e]; exact ha
  · rw [e]; exact hb

theorem projected {α β : Type} {out : Wire α} {k S} (h : Cone out k S) (lift : β → α)
    (nonconstant : ¬ Constant (cut lift out)) {raw pool : List (Wire β)} {n}
    (before : Build raw n pool) (cs : ∀ b : Bool,con b∈pool)
    (rep : Wire α → Wire β) (initial : ∀ w∈S,rep w∈pool)
    (improves : ∀ w∈S,CoDominance2590.Better (cut lift out) (cut lift w) (rep w)) :
    ∃ m ys, Build raw (n+m) ys ∧ cut lift out∈ys ∧ m+count (fun w => Constant (rep w)) S ≤ k := by
  classical
  induction h generalizing n pool rep with
  | stop =>
    have q := CoDominance2590.output (improves out (by simp))
    have nc : ¬Constant (rep out) := by simpa only [q] using nonconstant
    refine ⟨0,pool,by simpa using before,q ▸ initial out (by simp),?_⟩
    simp [count,nc]
  | @gate k U d a b fresh tail ih =>
    let z := op d a b
    let new := op d (rep a) (rep b)
    let r : Wire α → Wire β := fun w => if w=z then new else rep w
    have rz : r z=new := by simp [r]
    have ru (w) (hw : w∈U) : r w=rep w := by
      have ne : w≠z := fun e => fresh (show z∈U from e ▸ hw)
      simp [r,ne]
    have ha := initial a (Finset.mem_insert_self _ _)
    have hb := initial b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hu (w) (hw : w∈U) : rep w∈pool := initial w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))
    have good (w) (hw : w∈insert z U) : CoDominance2590.Better (cut lift out) (cut lift w) (r w) := by
      rcases Finset.mem_insert.mp hw with rfl|mem
      · rw [rz]
        exact CoDominance2590.gate d (improves a (Finset.mem_insert_self _ _))
          (improves b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
      · rw [ru _ mem]
        exact improves w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem))
    let P := fun w : Wire α => Constant (rep w)
    let Q := fun w : Wire α => Constant (r w)
    have unified : P a → P b → Q z := by
      rintro ⟨u,ua⟩ ⟨v,vb⟩
      refine ⟨if d then u || v else u && v,?_⟩
      change r z=_
      rw [rz]
      dsimp only [new]
      rw [ua,vb]
      rfl
    have amort := charge (P:=P) (Q:=Q) (a:=a) (b:=b) fresh
      (fun w hw => by change Constant (rep w) ↔ Constant (r w); rw [ru w hw]) unified
    by_cases free : P a ∨ P b
    · have nz : new∈pool := cheap cs d ha hb free
      have known (w) (hw : w∈insert z U) : r w∈pool := by
        rcases Finset.mem_insert.mp hw with rfl|hm
        · rw [rz]; exact nz
        · rw [ru _ hm]; exact hu _ hm
      obtain ⟨m,ys,built,outmem,spent⟩ := ih before cs r known good
      simp only [free,if_true,zero_add] at amort
      change count P (insert a (insert b U)) ≤ 1+count Q (insert z U) at amort
      change m+count Q (insert z U)≤k at spent
      exact ⟨m,ys,built,outmem,by change m+count P _≤_; omega⟩
    · let bank := new::pool
      have pre : Build raw (n+1) bank := Build.gate before d _ _ ha hb
      have known (w) (hw : w∈insert z U) : r w∈bank := by
        rcases Finset.mem_insert.mp hw with rfl|hm
        · rw [rz]; exact List.mem_cons_self
        · rw [ru _ hm]; exact List.mem_cons_of_mem _ (hu _ hm)
      obtain ⟨m,ys,built,outmem,spent⟩ := ih pre (fun v => List.mem_cons_of_mem _ (cs v)) r known good
      simp only [free,if_false] at amort
      change 1+count P (insert a (insert b U)) ≤ 1+count Q (insert z U) at amort
      change m+count Q (insert z U)≤k at spent
      refine ⟨m+1,ys,?_,outmem,?_⟩
      · exact (show n+1+m=n+(m+1) by omega) ▸ built
      · change m+1+count P _≤_
        omega

end
end CoDominanceLoss2590
