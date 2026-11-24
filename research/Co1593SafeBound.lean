import PEqualNP.Co1593NestedTrace

namespace Co1593NestedTrace

open Finset Co1593EmptyBudget Co1593StarCounting

variable {W V : Type*} [DecidableEq W] [DecidableEq V]

def one (T : W→Scope V) (x : V) (w : W) : Bool := decide (x∈T w)

theorem safe_lower [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (girth : ∀ v (c : G.Walk v v), c.IsCycle → 7 ≤ c.length)
    {I : Finset W} {T : W→Scope V} {isAnd : Step W→Bool} {gs B}
    (tr : Trace I T isAnd gs B) (raw : ∀ w∈I,(T w).card≤1)
    (out : W) (valid : out∈B) (noSingleton : T out=∅)
    (pairs : V→V→W→Bool) (goal : ∀ x y,G.Adj x y ↔ pairs x y out=true)
    (native : ∀ w∈I,∀ x y,pairs x y w=true → x∈T w ∨ y∈T w)
    (binary : ∀ g∈gs,∀ x y,pairs x y g.out=op (isAnd g) (pairs x y g.left) (pairs x y g.right))
    (safe : ∀ g∈gs,isAnd g=true → ∀ x∈T g.left,∀ y∈T g.right,G.Adj x y)
    (k : Nat) (cover : ∀ A : Finset V,(∀ x y,G.Adj x y → x∈A ∨ y∈A) → k≤A.card) :
    G.edgeSet.ncard+k ≤gs.length+1 := by
  classical
  let M := generators (empty T) gs {out}
  let L (i : Fin M.length) := T (M.get i).left
  let R (i : Fin M.length) := T (M.get i).right
  have data (i : Fin M.length) := member_data (empty T) gs {out} (M.get i) (List.get_mem M i)
  have flag (i : Fin M.length) : isAnd (M.get i)=true := by
    have d := data i
    have sc := local_scope tr (M.get i) d.1
    cases h : isAnd (M.get i)
    · have a : T (M.get i).out=∅ := of_decide_eq_true d.2.1
      have b : T (M.get i).left≠∅ := by simpa [empty] using d.2.2.1
      simp [h,a] at sc
      grind
    · rfl
  have left (i) : (L i).Nonempty := by
    have hh := (data i).2.2.1
    simpa [L,empty,Finset.nonempty_iff_ne_empty] using hh
  have right (i) : (R i).Nonempty := by
    have hh := (data i).2.2.2
    simpa [R,empty,Finset.nonempty_iff_ne_empty] using hh
  have monoOne (g) (hg : g∈gs) (x : V) : one T x g.out =
      op (isAnd g) (one T x g.left) (one T x g.right) := by
    have sc := local_scope tr g hg
    cases h : isAnd g
    · by_cases a : x∈T g.left <;> by_cases b : x∈T g.right <;> simp [one,op,sc,h,a,b]
    · by_cases a : x∈T g.left <;> by_cases b : x∈T g.right <;>
        simp [one,op,sc,h,a,b] <;> exact (G.loopless.irrefl x (safe g hg h x a x b)).elim
  have nonzero (x : V) (w) (h : one T x w=true) : empty T w=false := by
    have hx : x∈T w := of_decide_eq_true h
    have ne : T w≠∅ := Finset.nonempty_iff_ne_empty.mp ⟨x,hx⟩
    simp [empty,ne]
  have genModel (x y : V) : G.Adj x y ↔
      ∃ i,(x∈L i ∨ y∈L i) ∧ (x∈R i ∨ y∈R i) := by
    constructor
    · intro edge
      have rules (g) (hg : g∈gs) : ∀ b∈[pairs x y,one T x,one T y],
          b g.out=op (isAnd g) (b g.left) (b g.right) := by
        intro b hb
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
        rcases hb with rfl|rfl|rfl
        · exact binary g hg x y
        · exact monoOne g hg x
        · exact monoOne g hg y
      have allSafe (g) (hg : g∈gs) (hgAnd : isAnd g=true) : empty T g.out=true := by
        simp [empty,local_scope tr g hg,hgAnd]
      have ant : ∃ w∈({out}:Finset W),novel (pairs x y) (one T x) (one T y) w :=
        ⟨out,by simp,(goal x y).1 edge,by simp [one,noSingleton],by simp [one,noSingleton]⟩
      obtain good|⟨w,hw,pairOn,xOff,yOff⟩ :=
        produces (nonzero x) (nonzero y) gs {out} rules allSafe ant
      · obtain ⟨g,hg,cr⟩ := good
        obtain ⟨i,rfl⟩ := List.mem_iff_get.mp (show g∈M from hg)
        rcases cr with ⟨a,b⟩|⟨a,b⟩
        · exact ⟨i,Or.inl (of_decide_eq_true a),Or.inr (of_decide_eq_true b)⟩
        · exact ⟨i,Or.inr (of_decide_eq_true a),Or.inl (of_decide_eq_true b)⟩
      · have hi := back_inputs tr ({out}:Finset W) (by simpa using valid) hw
        rcases native w hi x y pairOn with h|h <;> simp [one,h] at *
    · rintro ⟨i,a,b⟩
      have ok : ∀ u∈L i,∀ v∈R i,G.Adj u v := safe (M.get i) (data i).1 (flag i)
      rcases a with a|a <;> rcases b with b|b
      · exact (G.loopless.irrefl x (ok x a x b)).elim
      · exact ok x a y b
      · exact (ok y a x b).symm
      · exact (G.loopless.irrefl y (ok y a y b)).elim
  obtain ⟨A,build,zero,known⟩ := lower_builds tr
  have avail (i) : L i∈A ∧ R i∈A :=
    ⟨known _ (all_wires tr _ (data i).1).1,known _ (all_wires tr _ (data i).1).2⟩
  have init : ∀ a∈insert ∅ (I.image T),a.card≤1 := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl|old
    · simp
    · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp old
      exact raw _ hw
  have both (g) (hg : g∈gs) (a : empty T g.left=true) (b : empty T g.right=true) : empty T g.out=true := by
    have l : T g.left=∅ := of_decide_eq_true a
    have r : T g.right=∅ := of_decide_eq_true b
    cases h : isAnd g <;> simp [empty,local_scope tr g hg,h,l,r]
  have lengths : M.length=births (empty T) gs {out} := generator_count _ _ _
  have joins : M.length ≤ (gs.map (other (empty T))).sum+1 := by
    rw [lengths]
    exact one_output (empty T) gs out both
  have cost := layered_count M.length girth L R left right genModel init build avail _ joins k cover
  have good (g) (hg : g∈gs) (a : isAnd g=false) (l : empty T g.left=false)
      (_ : empty T g.right=false) : empty T g.out=false := by
    have non : T g.left≠∅ := by simpa [empty] using l
    simp [empty,local_scope tr g hg,a,non]
  have size := spending T isAnd gs {out} good
  omega

end Co1593NestedTrace

#print axioms Co1593NestedTrace.safe_lower
