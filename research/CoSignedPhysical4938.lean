import PEqualNP.CoPetersenWedges4938
import PEqualNP.CoLeafBudget4938

namespace CoFormulaMinor4938

def Expr.scalar (x : Fin 10 → Bool) : Expr → Bool
  | .leaf v neg => if neg then !(x v) else x v
  | .fork op l r => if op then l.scalar x || r.scalar x else l.scalar x && r.scalar x

def scalarGraph (x : Fin 10 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
  (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 6 && x 8) || (x 7 && x 9) ||
  (x 8 && x 5) || (x 9 && x 6)

theorem bit_eval (t : Expr) (x : GInput) (k : Nat) (hk : k < 8) :
    (t.eval x).getLsbD k=t.scalar (fun v => (x v).getLsbD k) := by
  induction t with
  | leaf v n => cases n <;> simp [Expr.eval,Expr.scalar,BitVec.getLsbD_not,hk]
  | fork op a b ha hb =>
    cases op <;> simp [Expr.eval,Expr.scalar,gate,BitVec.getLsbD_or,BitVec.getLsbD_and,ha,hb]

theorem correct_words (t : Expr) (h : ∀ x,t.scalar x=scalarGraph x) : ∀ x : GInput,t.eval x=graph x := by
  intro x
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [bit_eval _ _ _ hi,h]
  simp only [graph,scalarGraph,BitVec.getLsbD_or,BitVec.getLsbD_and]

def localCount (p : Fin 10 → Option (Fin 3)) : Expr → Nat
  | .leaf v _ => if (p v).isSome then 1 else 0
  | .fork _ l r => localCount p l + localCount p r

def weight : Option Shape → Nat | none => 0 | some t => t.leaves

theorem glue_weight (op : Bool) (x y : Option Shape) :
    weight (glue op x y)=weight x+weight y := by
  cases x <;> cases y <;> simp [glue,weight,Shape.leaves]

theorem keep_weight (t : Expr) (p : Fin 10 → Option (Fin 3)) : weight (t.keep p)=localCount p t := by
  induction t with
  | leaf v n => cases h : p v <;> simp [Expr.keep,localCount,h,weight,Shape.leaves]
  | fork op a b ha hb => simp only [Expr.keep,localCount,glue_weight,ha,hb]

theorem real_wedge (t : Expr) (h : ∀ x, t.scalar x=scalarGraph x) (i : I) : 5 ≤ localCount (port i) t := by
  have all := all_required t (correct_words t h) i
  rw [←keep_weight]
  cases hs : t.keep (port i) with
  | none =>
    have a := all 168 (by decide +kernel)
    rw [hs] at a
    exact False.elim ((by decide : ¬ ((168 : Word)=0 ∨ (168 : Word)=255)) a)
  | some s =>
    exact wedge_five s (fun x hx => by simpa [hs,permits] using all x hx)

#print axioms real_wedge
end CoFormulaMinor4938

namespace CoFormulaMinor4938
abbrev Edge := Fin 15
def va : Edge → Fin 10 := ![0,1,2,3,4,0,1,2,3,4,5,6,7,8,9]
def vb : Edge → Fin 10 := ![1,2,3,4,0,5,6,7,8,9,7,8,9,5,6]
def forceOr : Edge → Nat := ![20,9,18,5,10,130,257,34,36,65,5,10,20,9,18]
def pairPort (e : Edge) (v : Fin 10) : Option (Fin 3) :=
  if v=va e then some 0 else if v=vb e then some 1 else none
def pairTest (e : Edge) (d : Bool) (v : Fin 10) : Word :=
  match pairPort e v with
  | some a => lit a
  | none => if d && (forceOr e).testBit v.val then 255 else 0

theorem edge_rows : ∀ (e : Edge) (d : Bool),graph (pairTest e d)=(if d then 238 else 136) := by
  intro e
  fin_cases e <;> decide +kernel
theorem pair_sound (e : Edge) (d : Bool) : ∀ v, match pairPort e v with
    | some a => pairTest e d v=lit a | none => pairTest e d v=0 ∨ pairTest e d v=255 := by
  intro v
  cases hp : pairPort e v with
  | some a => simp [pairTest,hp]
  | none => cases h : (d && (forceOr e).testBit v.val) <;> simp [pairTest,hp,h]

theorem incompatible : (cat1++cat2).all (fun T => !(T.contains 136 && T.contains 238))=true := by decide +kernel

theorem real_edge (t : Expr) (h : ∀ x,t.scalar x=scalarGraph x) (e : Edge) :
    3 ≤ localCount (pairPort e) t := by
  have two (d : Bool) : permits (t.keep (pairPort e)) (if d then 238 else 136) := by
    have f := restriction t (pairTest e d) (pairPort e) (pair_sound e d)
    rwa [correct_words t h,edge_rows] at f
  rw [←keep_weight]
  cases hs : t.keep (pairPort e) with
  | none =>
    have a := two false
    rw [hs] at a
    exact False.elim ((by decide : ¬ ((136 : Word)=0 ∨ (136 : Word)=255)) a)
  | some s =>
    change 3 ≤ s.leaves
    by_contra! short
    have pos := nonempty s
    obtain ⟨T,ht,all⟩ := bounded_four s (by omega)
    have small : s.leaves=1 ∨ s.leaves=2 := by omega
    have inlist : T∈cat1++cat2 := by
      rcases small with r|r
      · apply List.mem_append_left; simpa [levels,r] using ht
      · apply List.mem_append_right; simpa [levels,r] using ht
    have impossible := List.all_eq_true.mp incompatible T inlist
    have a : (136 : Word)∈s.value := by simpa [hs,permits] using two false
    have b : (238 : Word)∈s.value := by simpa [hs,permits] using two true
    simp at impossible
    exact impossible.elim (fun no => no (all 136 a)) (fun no => no (all 238 b))
#print axioms real_edge
end CoFormulaMinor4938

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
