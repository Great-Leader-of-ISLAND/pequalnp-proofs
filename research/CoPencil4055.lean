import PEqualNP.CoSensitivity4055

namespace CoPencil4055
open CoSensitivity4055
abbrev V := Fin 42
abbrev P := Fin 21
abbrev X := V → Bool

def incident (p l : P) : Bool :=
  [((p:Nat)+20)%21,p.val,(p.val+5)%21,(p.val+7)%21,(p.val+17)%21].contains l.val

def independent (x : X) : Prop :=
  ∀ p l : P, incident p l=true → x (Fin.castAdd 21 p)=false ∨ x (Fin.natAdd 21 l)=false

def edge (p l : P) : X := fun v => decide (v=Fin.castAdd 21 p ∨ v=Fin.natAdd 21 l)
def baseline (v : V) := ([1,4,14,16,26,28,38,41] : List Nat).contains v.val
def sample (r : Option V) : X :=
  match r with
  | none => baseline
  | some i => fun v => baseline v || decide (v=i)
def vertex (i : V) : Word V := fun r => sample r i
def sources : List (Word V) := List.ofFn vertex++[zero]

theorem maximal : independent baseline ∧
    (∀ y : X, independent y → (∀ i,baseline i=true → y i=true) → y=baseline) := by
  have good : independent baseline := by decide +kernel
  have cover : ∀ v : V, baseline v=false →
      ∃ p l : P, incident p l=true ∧ (∀ i : V,edge p l i=true → sample (some v) i=true) := by
    decide +kernel
  refine ⟨good,?_⟩
  intro y clean grow
  funext v
  cases b : baseline v with
  | true => exact grow v b
  | false =>
    apply Bool.eq_false_iff.mpr
    intro hv
    obtain ⟨p,l,inc,on⟩ := cover v b
    have inside (i : V) (e : edge p l i=true) : y i=true := by
      have h := on i e
      change (baseline i || decide (i=v))=true at h
      simp only [Bool.or_eq_true,decide_eq_true_eq] at h
      rcases h with base|rfl
      · exact grow i base
      · exact hv
    rcases clean p l inc with no|no
    · exact Bool.noConfusion ((inside _ (by simp [edge])).symm.trans no)
    · exact Bool.noConfusion ((inside _ (by simp [edge])).symm.trans no)

def scalar (ws : List Bool) (s : Finset Nat) := decide (∀ j∈s,ws.getD j false=true)
def tick (ws : List Bool) (r : Rule) := ws++[scalar ws r.1 || scalar ws r.2]
def value (rs : List Rule) (out : Finset Nat) (x : X) :=
  scalar (rs.foldl tick (List.ofFn x++[false])) out

private theorem read_project (ws : List (Word V)) (r : Option V) (j : Nat) :
    (ws.map (fun w => w r)).getD j false = (ws.getD j zero) r := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[j]? <;> rfl

private theorem project (ws : List (Word V)) (r : Option V) (s : Finset Nat) :
    scalar (ws.map (fun w => w r)) s = conjunction ws s r := by simp only [scalar,conjunction,read_project]

private theorem history (rs : List Rule) (ws : List (Word V)) (r : Option V) :
    (rs.foldl signal ws).map (fun w => w r) = rs.foldl tick (ws.map fun w => w r) := by
  induction rs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    change ((gs.foldl signal (signal ws g)).map _) = _
    rw [ih]
    simp only [List.foldl_cons,signal,tick,List.map_append,List.map_cons,List.map_nil,step,project]

theorem pointwise (rs : List Rule) (out : Finset Nat) (r : Option V) :
    conjunction (rs.foldl signal sources) out r = value rs out (sample r) := by
  rw [←project,history]
  simp [value,sources,vertex,zero,List.map_ofFn,Function.comp_def]

private theorem scalar_mono (us vs : List Bool) (s : Finset Nat)
    (le : ∀ j,us.getD j false=true → vs.getD j false=true) :
    scalar us s=true → scalar vs s=true := by
  simp only [scalar,decide_eq_true_eq]
  intro h j hj
  exact le j (h j hj)

def Rel (a b : List Bool) := a.length=b.length ∧ ∀ j,a.getD j false=true → b.getD j false=true

private theorem append_rel {a b : List Bool} {u v : Bool} (h : Rel a b) (hu : u=true → v=true) :
    Rel (a++[u]) (b++[v]) := by
  refine ⟨by simp [h.1],?_⟩
  intro j
  by_cases lo : j<a.length
  · have lb : j<b.length := h.1 ▸ lo
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_left lo,List.getElem?_append_left lb] using h.2 j
  · have hb : b.length≤j := by omega
    have ha : a.length≤j := by omega
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right ha,List.getElem?_append_right hb,←h.1]
    cases j-a.length <;> simp_all

theorem monotone (rs : List Rule) (out : Finset Nat) {x y : X}
    (h : ∀ i,x i=true → y i=true) : value rs out x=true → value rs out y=true := by
  have raw : Rel (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp,?_⟩
    intro j
    by_cases hj : j<42
    · simpa only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hj,↓reduceDIte,Option.getD_some] using h ⟨j,hj⟩
    · simp [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hj]
  have front (rs : List Rule) (a b : List Bool) (le : Rel a b) :
      Rel (rs.foldl tick a) (rs.foldl tick b) := by
    induction rs generalizing a b with
    | nil => exact le
    | cons g gs ih =>
      apply ih
      apply append_rel le
      simp only [Bool.or_eq_true]
      exact Or.imp (scalar_mono a b _ le.2) (scalar_mono a b _ le.2)
  exact scalar_mono _ _ out (front rs _ _ (append_rel raw id)).2

theorem lower (rs : List Rule) (out : Finset Nat)
    (yes : ∀ p l,incident p l=true → value rs out (edge p l)=true)
    (no : ∀ x : X,independent x → (∀ y : X,independent y →
      (∀ i,x i=true → y i=true) → y=x) → value rs out x=false) : 33 ≤ rs.length := by
  let z := conjunction (rs.foldl signal sources) out
  have off : z none=false := (pointwise rs out none).trans (no baseline maximal.1 maximal.2)
  have cover : ∀ v : V, baseline v=false →
      ∃ p l : P, incident p l=true ∧ (∀ i : V,edge p l i=true → sample (some v) i=true) := by decide +kernel
  have h0 : ∀ v : V,baseline v=false → z (some v)=true := by
    intro v hv
    obtain ⟨p,l,inc,h⟩ := cover v hv
    exact (pointwise rs out (some v)).trans (monotone rs out h (yes p l inc))
  let outside := Finset.univ.filter (fun v : V => baseline v=false)
  have sz : outside.card=34 := by decide +kernel
  have sub : outside⊆changes z := by
    intro v hv
    simp only [changes,off,Bool.false_eq_true,↓reduceIte,Finset.mem_filter,Finset.mem_univ,true_and]
    exact h0 v (Finset.mem_filter.mp hv).2
  have bi := Finset.card_le_card sub
  have init : ∀ w∈sources,(changes w).card≤1 := by
    intro w hw
    rcases List.mem_append.mp hw with m|m
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp m
      exact (by decide +kernel : ∀ i : V,(changes (vertex i)).card≤1) i
    · obtain rfl := List.mem_singleton.mp m
      simp [changes,zero]
  have cap := cost rs out sources init
  change (changes z).card ≤ rs.length+1 at cap
  omega
#print axioms lower
end CoPencil4055
