import PEqualNP.Co4358Trail
import PEqualNP.CoAO3143MemoWord

namespace CoNum4358
open CoAO3143

def project (bk : List Sig) (S : Finset Nat) : Finset Sig := S.image (lookupKW bk)

def charge (g : Gate) : Nat := if g.isOr && (g.a == 2 || g.b == 2) then 1 else 0

/-- A trace records true original pin names, and uses the relaxed six-row sets
    at each gate. Its local original-signal claims are independently checked
    by the signed lower bound and ordinary KW protocol lemmas in the caller. -/
inductive Walk : Nat → Nat → List Sig → List LiftSet → Finset Nat → Prop
  | done (q : Nat) (bk : List Sig) (bs : List LiftSet) (i : Nat)
      (orig : lookupKW bk i = target) (raised : (3 : LiftVal) ∈ bs.getD i []) :
      Walk 0 q bk bs {i}
  | step {k q : Nat} {bk : List Sig} {bs : List LiftSet} {U : Finset Nat}
      (g : Gate) (sorted : g.a < g.b) (budget : charge g ≤ q)
      (fresh : gateAvailable bk (g.kw bk) = true)
      (live : Live (k+1) 0 (project bk (insert g.a (insert g.b U))))
      (child : Walk k (q-charge g) (bk ++ [g.kw bk]) (bs ++ [g.loose bs]) (insert bk.length U)) :
      Walk (k+1) q bk bs (insert g.a (insert g.b U))

def residual (xs : List Nat) (a b : Nat) (ka kb : Bool) : List Nat :=
  xs.filter fun i => (i != a || ka) && (i != b || kb)

theorem residual_set {xs : List Nat} {U : Finset Nat} {a b : Nat}
    (sub : xs.toFinset = insert a (insert b U)) :
    (residual xs a b (decide (a∈U)) (decide (b∈U))).toFinset = U := by
  ext x
  have mem : x∈xs ↔ x=a ∨ x=b ∨ x∈U := by
    rw [← List.mem_toFinset,sub]
    simp
  simp only [List.mem_toFinset,List.mem_filter,residual,Bool.and_eq_true,Bool.or_eq_true,
    bne_iff_ne,decide_eq_true_eq,mem]
  by_cases xa : x=a <;> by_cases xb : x=b <;> subst_vars <;> aesop

def thisGrid := ProtocolProof.grid 7 8

def admissible (k : Nat) (bk : List Sig) (xs : List Nat) : Bool :=
  let ws := (xs.map (lookupKW bk)).dedup
  decide (ws.length ≤ k+1) && (unionSep false ws == top) &&
    !(ws.length == k+1 && Memo.wordCotree thisGrid ws)

theorem admissible_of_live {k bk xs} (h : Live k 0 (project bk xs.toFinset)) :
    admissible k bk xs = true := by
  let ws := (xs.map (lookupKW bk)).dedup
  have hset : ws.toFinset = project bk xs.toFinset := by
    ext w
    simp [ws,project]
  have nodup : ws.Nodup := List.nodup_dedup _
  have card := List.toFinset_card_of_nodup nodup
  have hr : Live k 0 ws.toFinset := by rwa [hset]
  have width := ProtocolProof.width hr
  have cov : unionSep false ws=top := live_cover hr rfl
  have check : (ws.length == k+1 && Memo.wordCotree thisGrid ws)=false := by
    apply Bool.eq_false_iff.mpr
    intro hbad
    simp only [Bool.and_eq_true,beq_iff_eq] at hbad
    exact Bool.false_ne_true ((Memo.wordCotree_false hr (by omega) thisGrid).symm.trans hbad.2)
  change (decide (ws.length≤k+1) && (unionSep false ws==top) &&
    !(ws.length==k+1 && Memo.wordCotree thisGrid ws))=true
  rw [check,cov]
  simp [show ws.length≤k+1 by omega]

def options : List Bool := [false,true]

theorem all_options (b : Bool) : b∈options := by cases b <;> simp [options]

def stepOne (next : Nat → List Sig → List LiftSet → List Nat → Bool)
    (q : Nat) (bk : List Sig) (bs : List LiftSet) (xs : List Nat) (g : Gate) : Bool :=
  decide (g.a<g.b) && decide (charge g≤q) && gateAvailable bk (g.kw bk) &&
    options.any fun keepA => options.any fun keepB =>
      next (q-charge g) (bk ++ [g.kw bk]) (bs ++ [g.loose bs])
        (bk.length :: residual xs g.a g.b keepA keepB)

def explore : Nat → Nat → List Sig → List LiftSet → List Nat → Bool
  | 0,_,bk,bs,xs => xs.any fun i => lookupKW bk i == target && (bs.getD i []).contains 3
  | k+1,q,bk,bs,xs =>
    admissible (k+1) bk xs && xs.any fun a => xs.any fun b => options.any fun d =>
      stepOne (explore k) q bk bs xs ⟨d,a,b⟩

theorem explore_complete {k q bk bs S} (w : Walk k q bk bs S) (xs : List Nat)
    (hxs : xs.toFinset=S) : explore k q bk bs xs=true := by
  induction w generalizing xs with
  | done q bk bs i orig raised =>
    apply List.any_eq_true.mpr
    refine ⟨i,?_,?_⟩
    · have : i∈xs.toFinset := by rw [hxs]; simp
      simpa using this
    · simpa [orig] using raised
  | @step k q bk bs U g sorted budget fresh live child ih =>
    rw [explore,Bool.and_eq_true]
    refine ⟨admissible_of_live (by rwa [hxs]),?_⟩
    have am : g.a∈xs := by
      have : g.a∈xs.toFinset := by rw [hxs]; simp
      simpa using this
    have bm : g.b∈xs := by
      have : g.b∈xs.toFinset := by rw [hxs]; simp
      simpa using this
    apply List.any_eq_true.mpr
    refine ⟨g.a,am,List.any_eq_true.mpr ⟨g.b,bm,List.any_eq_true.mpr ⟨g.isOr,all_options _,?_⟩⟩⟩
    change stepOne (explore k) q bk bs xs g = true
    simp only [stepOne,sorted,budget,fresh,decide_true,Bool.true_and]
    apply List.any_eq_true.mpr
    refine ⟨decide (g.a∈U),all_options _,List.any_eq_true.mpr ⟨decide (g.b∈U),all_options _,?_⟩⟩
    apply ih
    simp [residual_set hxs]

end CoNum4358
