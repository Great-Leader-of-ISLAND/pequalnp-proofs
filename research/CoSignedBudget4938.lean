import PEqualNP.CoSignedEdge4938
import PEqualNP.CoLeafBudget4938

namespace CoFormulaMinor4938
open CoLeafBudget4938

def mult (v : V) : Expr → Nat
  | .leaf u _ => if v=u then 1 else 0
  | .fork _ l r => mult v l + mult v r

def total : Expr → Nat | .leaf _ _ => 1 | .fork _ l r => total l + total r

theorem add_counts (f g : V → Nat) : count (fun v => f v+g v)=count f+count g := by
  unfold count
  generalize List.finRange 10 = xs
  induction xs with
  | nil => rfl
  | cons v xs h => simp only [List.map_cons,List.sum_cons];omega

theorem finite_atom : ∀ v : V,count (fun u => if u=v then 1 else 0)=1 := by decide +kernel

theorem total_eq (t : Expr) : count (fun v => mult v t)=total t := by
  induction t with
  | leaf i b => exact finite_atom i
  | fork op a b ha hb => simp only [mult,total,add_counts,ha,hb]

theorem edge_atom : ∀ (e : Edge) (u : V), (if (pairPort e u).isSome then 1 else 0) =
    (if va e=u then 1 else 0)+(if vb e=u then 1 else 0) := by decide +kernel
theorem wedge_atom : ∀ (i : I) (u : V), (if (port i u).isSome then 1 else 0) =
    (if center i=u then 1 else 0)+(if left i=u then 1 else 0)+(if right i=u then 1 else 0) := by decide +kernel

theorem edge_count (t : Expr) (e : Edge) :
    localCount (pairPort e) t=mult (va e) t+mult (vb e) t := by
  induction t with
  | leaf v n => exact edge_atom e v
  | fork op a b ha hb => simp only [localCount,mult,ha,hb];omega

theorem wedge_count (t : Expr) (i : I) :
    localCount (port i) t=mult (center i) t+mult (left i) t+mult (right i) t := by
  induction t with
  | leaf v n => exact wedge_atom i v
  | fork op a b ha hb => simp only [localCount,mult,ha,hb];omega

theorem absent_eval (t : Expr) (v : V) (h : mult v t=0) (x y : V → Bool)
    (eq : ∀ u,u≠v → x u=y u) : t.scalar x=t.scalar y := by
  induction t with
  | leaf u n =>
    by_cases same : u=v
    · subst u;simp [mult] at h
    · simp [Expr.scalar,eq u same]
  | fork op l r hl hr =>
    change mult v l + mult v r=0 at h
    simp only [Expr.scalar,hl (by omega),hr (by omega)]

theorem sensitive : ∀ v : V,∃ u : V,scalarGraph (fun i => decide (i=u))=false ∧
    scalarGraph (fun i => decide (i=u ∨ i=v))=true := by decide +kernel

theorem positive_mult (t : Expr) (h : ∀ x,t.scalar x=scalarGraph x) (v : V) : 1 ≤ mult v t := by
  by_contra! low
  obtain ⟨u,zero,one⟩ := sensitive v
  have eq := absent_eval t v (by omega) (fun i => decide (i=u)) (fun i => decide (i=u ∨ i=v))
    (fun i ne => by simp [ne])
  simp [h,zero,one] at eq

theorem pair_labels : ∀ u v : V, near u v=true → ∃ e : Edge,(va e=u ∧ vb e=v) ∨ (va e=v ∧ vb e=u) := by decide +kernel
theorem wedges_labels (S : V → Bool) : ∀ v : V, 2 ≤ neighbors S v → ∃ i : I,
    center i=v ∧ S (left i)=true ∧ S (right i)=true := by
  intro v
  have finite : ∀ (v : V) (S : V → Bool),2 ≤ neighbors S v → ∃ i : I,
      center i=v ∧ S (left i)=true ∧ S (right i)=true := by
    intro z
    fin_cases z <;> decide +kernel
  exact finite v S

def singlesOf (t : Expr) (v : V) := decide (mult v t=1)

theorem singleton_independent (t : Expr) (h : ∀ x,t.scalar x=scalarGraph x) : isolated (singlesOf t)=true := by
  apply List.all_eq_true.mpr
  intro v _
  apply List.all_eq_true.mpr
  intro u _
  cases a : singlesOf t v <;> cases b : singlesOf t u <;> cases c : near v u <;> simp [a,b,c]
  have av : mult v t=1 := of_decide_eq_true a
  have bv : mult u t=1 := of_decide_eq_true b
  obtain ⟨e,f|f⟩ := pair_labels v u c <;>
    have lim := real_edge t h e <;> rw [edge_count,f.1,f.2] at lim <;> omega

theorem eighteen (t : Expr) (h : ∀ x,t.scalar x=scalarGraph x) : 18 ≤ total t := by
  rw [←total_eq]
  apply lower _ (singlesOf t) (singleton_independent t h)
  intro v
  have pos := positive_mult t h v
  by_cases one : mult v t=1
  · simp [need,singlesOf,one]
  · by_cases two : 2 ≤ neighbors (singlesOf t) v
    · obtain ⟨i,vv,a,b⟩ := wedges_labels _ v two
      have l : mult (left i) t=1 := of_decide_eq_true a
      have r : mult (right i) t=1 := of_decide_eq_true b
      have lim := real_wedge t h i
      rw [wedge_count,vv,l,r] at lim
      simp [need,singlesOf,one] at *
      omega
    · simp [need,show singlesOf t v=false by simp [singlesOf,one],two]
      omega

#print axioms eighteen
end CoFormulaMinor4938
