import PEqualNP.Defs

/- Bottom OR gates in a one-AND-level circuit can be shared without charge duplication
only inside a single star of a square-free graph. -/
namespace Co1593StarCounting

open Finset

variable {V : Type*} [DecidableEq V]

abbrev Scope (V : Type*) := Finset V
structure Join (V : Type*) where
  left : Scope V
  right : Scope V

def Join.out (g : Join V) := g.left ∪ g.right

inductive Build (initial : Finset (Scope V)) : List (Join V) → Finset (Scope V) → Prop where
  | start : Build initial [] initial
  | add {gs B} (pre : Build initial gs B) (g : Join V)
      (ha : g.left ∈ B) (hb : g.right ∈ B) : Build initial (g::gs) (insert g.out B)

def paid (U : Scope V) (g : Join V) : Bool := decide (2 ≤ g.out.card ∧ g.out ⊆ U)

def total (D : Finset (Scope V)) : Scope V := D.biUnion id

private theorem total_insert (s : Scope V) (D : Finset (Scope V)) :
    total (insert s D) = s ∪ total D := by simp [total]

private theorem small_total (D : Finset (Scope V)) (sml : ∀ a∈D, a.card≤1) :
    (total D).card ≤ D.card := by
  induction D using Finset.induction_on with
  | empty => simp [total]
  | @insert a D ha ih =>
    have h₁ := sml a (Finset.mem_insert_self _ _)
    have h₂ := ih (fun b hb => sml b (Finset.mem_insert_of_mem hb))
    rw [total_insert, Finset.card_insert_of_notMem ha]
    have h := Finset.card_union_le a (total D)
    omega

theorem scoped_count {I : Finset (Scope V)} (raw : ∀ a∈I, a.card≤1)
    {gs B} (run : Build I gs B) (U : Scope V) (D : Finset (Scope V))
    (sub : D ⊆ B) (inU : ∀ a∈D, a⊆U) :
    (total D).card ≤ D.card + (gs.filter (paid U)).length := by
  induction run generalizing D with
  | start => simpa using small_total D (fun a ha => raw a (sub ha))
  | @add gs B pre g ha hb ih =>
    have step : (gs.filter (paid U)).length ≤ ((g::gs).filter (paid U)).length := by
      cases h : paid U g <;> simp [List.filter_cons,h]
    by_cases active : g.out ∈ D
    · let E := D.erase g.out
      have back : insert g.out E = D := Finset.insert_erase active
      have EB : E ⊆ B := by
        intro a ae
        rcases Finset.mem_insert.mp (sub (Finset.mem_of_mem_erase ae)) with eq|ok
        · exact (Finset.ne_of_mem_erase ae eq).elim
        · exact ok
      have EU : ∀ a∈E,a⊆U := fun a ae => inU a (Finset.mem_of_mem_erase ae)
      have sz : E.card+1=D.card := Finset.card_erase_add_one active
      by_cases big : 2 ≤ g.out.card
      · let F := insert g.left (insert g.right E)
        have FB : F⊆B := Finset.insert_subset ha (Finset.insert_subset hb EB)
        have Uo := inU g.out active
        have FU : ∀ a∈F,a⊆U := by
          intro a af
          rcases Finset.mem_insert.mp af with rfl|af
          · exact fun x h => Uo (Finset.mem_union_left _ h)
          rcases Finset.mem_insert.mp af with rfl|ae
          · exact fun x h => Uo (Finset.mem_union_right _ h)
          · exact EU _ ae
        have eq : total D=total F := by
          rw [←back,total_insert]
          simp [F,total_insert,Join.out,Finset.union_assoc]
        have h₁ := Finset.card_insert_le g.left (insert g.right E)
        have h₂ := Finset.card_insert_le g.right E
        have bound : F.card ≤ D.card+1 := by dsimp [F]; omega
        have p : paid U g=true := by simp [paid,big,Uo]
        have rec := ih F FB FU
        rw [eq]
        simp only [List.filter_cons,p, ↓reduceIte,List.length_cons]
        omega
      · have rec := ih E EB EU
        have union_le := Finset.card_union_le g.out (total E)
        have eq : total D = g.out ∪ total E := by rw [←back,total_insert]
        rw [eq]
        omega
    · have DB : D⊆B := by
        intro a ad
        rcases Finset.mem_insert.mp (sub ad) with eq|ok
        · exact (active (eq ▸ ad)).elim
        · exact ok
      exact le_trans (ih D DB inU) (Nat.add_le_add_left step _)

/-- A gate counted for two different centers would display a four-cycle. -/
theorem unique_center {G : SimpleGraph V}
    (squareFree : ∀ p q a b : V, p≠q → a≠b → G.Adj p a → G.Adj p b →
      G.Adj q a → G.Adj q b → False)
    {p q : V} {s : Scope V} (large : 2 ≤ s.card)
    (hp : ∀ x∈s,G.Adj p x) (hq : ∀ x∈s,G.Adj q x) : p=q := by
  by_contra distinct
  obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp (show 1<s.card by omega)
  exact squareFree p q a b distinct ab (hp a ha) (hp b hb) (hq a ha) (hq b hb)

theorem no_square_of_girth_seven {G : SimpleGraph V}
    (girth : ∀ v (c : G.Walk v v), c.IsCycle → 7 ≤ c.length)
    (p q a b : V) (pq : p≠q) (ab : a≠b) (pa : G.Adj p a) (pb : G.Adj p b)
    (qa : G.Adj q a) (qb : G.Adj q b) : False := by
  let W : G.Walk p p := .cons pa (.cons qa.symm (.cons qb (.cons pb.symm .nil)))
  have len : W.length=4 := rfl
  have cyc : W.IsCycle := by
    apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨?_,by omega⟩
    simp only [W,SimpleGraph.Walk.tail_cons,SimpleGraph.Walk.isPath_copy,
      SimpleGraph.Walk.isPath_def,SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil]
    simp [ab,pa.ne.symm,qa.ne.symm,qb.ne,pb.ne.symm,pq.symm]
  have h := girth p W cyc
  omega

def Cost (gs : List (Join V)) (U : Scope V) := (gs.filter (paid U)).length

private theorem cost_cons (g : Join V) (gs : List (Join V)) (U : Scope V) :
    Cost (g::gs) U = Cost gs U + (if paid U g then 1 else 0) := by
  cases h : paid U g <;> simp [Cost,List.filter_cons,h]

theorem no_double_charge {G : SimpleGraph V}
    (girth : ∀ v (c : G.Walk v v), c.IsCycle → 7 ≤ c.length)
    (K : Finset V) (U : V → Scope V) (safe : ∀ c∈K,∀ x∈U c,G.Adj c x)
    (gs : List (Join V)) : (∑ c ∈ K, Cost gs (U c)) ≤ gs.length := by
  classical
  induction gs with
  | nil => simp [Cost]
  | cons g gs ih =>
    have card : (K.filter (fun c => paid (U c) g = true)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      obtain ⟨ak,ag⟩ := Finset.mem_filter.mp ha
      obtain ⟨bk,bg⟩ := Finset.mem_filter.mp hb
      have A : 2 ≤ g.out.card ∧ g.out ⊆ U a := of_decide_eq_true ag
      have B : 2 ≤ g.out.card ∧ g.out ⊆ U b := of_decide_eq_true bg
      exact unique_center (no_square_of_girth_seven girth) A.1
        (fun x hx => safe a ak x (A.2 hx)) (fun x hx => safe b bk x (B.2 hx))
    have eq : (∑ c ∈ K, (if paid (U c) g then 1 else 0 : Nat)) =
        (K.filter (fun c => paid (U c) g = true)).card := by simp
    simp only [cost_cons,Finset.sum_add_distrib,List.length_cons]
    omega

/-- The bottom gates and the AND gates together pay for all assigned edge leaves.
    A scope may feed several ANDs at one center, and a bottom OR gate may fan out. -/
theorem stars_pay_for_leaves {G : SimpleGraph V}
    (girth : ∀ v (c : G.Walk v v), c.IsCycle → 7 ≤ c.length)
    (K : Finset V) (U : V → Scope V) (safe : ∀ c∈K,∀ x∈U c,G.Adj c x)
    {I : Finset (Scope V)} (raw : ∀ a∈I, a.card≤1)
    {gs B} (run : Build I gs B) (D : V → Finset (Scope V))
    (sub : ∀ c∈K,D c⊆B) (inU : ∀ c∈K,∀ a∈D c,a⊆U c) :
    (∑ c ∈ K, (total (D c)).card) ≤ (∑ c ∈ K, (D c).card) + gs.length := by
  have localBound (c) (hc : c∈K) : (total (D c)).card ≤ (D c).card+Cost gs (U c) :=
    scoped_count raw run (U c) (D c) (sub c hc) (inU c hc)
  have h₁ := Finset.sum_le_sum localBound
  have h₂ := no_double_charge girth K U safe gs
  rw [Finset.sum_add_distrib] at h₁
  omega

/-- Any complete bipartite product contained in a graph of girth at least seven is a star. -/
theorem product_has_single_side {G : SimpleGraph V}
    (girth : ∀ v (c : G.Walk v v), c.IsCycle → 7 ≤ c.length)
    {a b : Scope V} (safe : ∀ x∈a,∀ y∈b,G.Adj x y) : a.card≤1 ∨ b.card≤1 := by
  by_contra! large
  obtain ⟨p,hp,q,hq,pq⟩ := Finset.one_lt_card.mp large.1
  obtain ⟨r,hr,s,hs,rs⟩ := Finset.one_lt_card.mp large.2
  exact no_square_of_girth_seven girth p q r s pq rs
    (safe p hp r hr) (safe p hp s hs) (safe q hq r hr) (safe q hq s hs)

theorem join_output_count {I : Finset (Scope V)} (raw : ∀ a∈I, a.card≤1)
    {gs B} (run : Build I gs B) (s : Scope V) (wire : s∈B) : s.card≤gs.length+1 := by
  have h := scoped_count raw run s {s} (by simpa using wire)
    (by intro t ht; obtain rfl := Finset.mem_singleton.mp ht; exact fun _ hx => hx)
  have hfilter : (gs.filter (paid s)).length ≤ gs.length := List.length_filter_le ..
  simpa [total] using (show (total ({s}:Finset (Scope V))).card ≤ gs.length+1 by
    simp only [Finset.card_singleton] at h; omega)

/-- Exact lower-bound direction for a normalized set of stars, with arbitrary sharing
    in its lower and upper OR DAGs.  An arbitrary gate count may also include duplicate
    stars, accounted for by `allocated`. -/
theorem counting_lower [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (girth : ∀ v (c : G.Walk v v), c.IsCycle → 7 ≤ c.length)
    (K : Finset V) (D : V → Finset (Scope V))
    (liveCenter : ∀ c∈K,(D c).Nonempty)
    (model : ∀ x y, G.Adj x y ↔
      (x∈K ∧ y∈total (D x)) ∨ (y∈K ∧ x∈total (D y)))
    {I : Finset (Scope V)} (raw : ∀ a∈I,a.card≤1)
    {gs B} (run : Build I gs B) (sub : ∀ c∈K,D c ⊆ B)
    (k binary top : Nat) (cover : ∀ T : Finset V,(∀ x y,G.Adj x y → x∈T ∨ y∈T) → k≤T.card)
    (allocated : (∑ c ∈ K, (D c).card) ≤ binary) (joinCost : binary ≤ top+1) :
    G.edgeSet.ncard+k ≤ gs.length+binary+top+1 := by
  classical
  have cap := stars_pay_for_leaves girth K (fun c => total (D c))
    (fun c hc x hx => (model c x).2 (Or.inl ⟨hc,hx⟩)) raw run D sub
    (fun c _ a ha x hx => Finset.mem_biUnion.mpr ⟨a,ha,hx⟩)
  let S := K.biUnion fun c => (total (D c)).image (fun x => s(c,x))
  have Esub : G.edgeFinset ⊆ S := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hadj : G.Adj a b := (SimpleGraph.mem_edgeFinset.mp he)
      rcases (model a b).1 hadj with h|h
      · exact Finset.mem_biUnion.mpr ⟨a,h.1,Finset.mem_image.mpr ⟨b,h.2,rfl⟩⟩
      · exact Finset.mem_biUnion.mpr ⟨b,h.1,Finset.mem_image.mpr ⟨a,h.2,Sym2.eq_swap⟩⟩
  have ce : G.edgeSet.ncard=G.edgeFinset.card := Set.ncard_eq_toFinset_card' _
  have ee : G.edgeFinset.card ≤ ∑ c ∈ K, (total (D c)).card :=
    (Finset.card_le_card Esub).trans (Finset.card_biUnion_le.trans
      (Finset.sum_le_sum fun c _ => Finset.card_image_le))
  have kk := cover K (fun x y e => ((model x y).1 e).imp And.left And.left)
  have nonemptySum : K.card ≤ ∑ c ∈ K, (D c).card := by
    calc
      K.card = ∑ _ ∈ K, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun c hc => Finset.card_pos.mpr (liveCenter c hc))
  omega

end Co1593StarCounting
