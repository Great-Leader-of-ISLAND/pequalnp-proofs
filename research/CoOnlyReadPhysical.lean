import Mathlib
import PEqualNP.Defs

namespace CoOnlyReadPhysical
open PEqualNP.CircuitLowerBounds

def value (g : Gate) (ws : List Bool) := g.op.eval (g.inputs.map (fun i => ws.getD i false))
def run (gs : List Gate) (ws : List Bool) := gs.foldl (fun t g => t++[value g t]) ws

private theorem other_index (front back : List Bool) (p q : Bool) (k : Nat)
    (ne : k≠front.length) :
    (front++p::back).getD k false = (front++q::back).getD k false := by
  induction front generalizing k with
  | nil => cases k <;> simp_all
  | cons a f ih =>
    cases k with
    | zero => rfl
    | succ j =>
      change (f++p::back).getD j false=(f++q::back).getD j false
      exact ih j (fun eq => ne (by simp [eq]))

private theorem pivot_index (front back : List Bool) (p : Bool) :
    (front++p::back).getD front.length false=p := by
  induction front with
  | nil => rfl
  | cons a f ih => exact ih

theorem scanWithout (gs : List Gate) (front rear : List Bool)
    (noneRead : ∀ g∈gs, front.length∉g.inputs) :
    ∃ after : List Bool, ∀ p : Bool, run gs (front++p::rear)=front++p::after := by
  induction gs generalizing rear with
  | nil => exact ⟨rear,fun _ => rfl⟩
  | cons g gs ih =>
    let z := value g (front++false::rear)
    have eqv (p : Bool) : value g (front++p::rear)=z := by
      unfold value
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro k hk
      exact other_index front rear p false k (fun eq => noneRead g (by simp) (eq ▸ hk))
    obtain ⟨after,ha⟩ := ih (rear++[z]) (fun h hh => noneRead h (by simp [hh]))
    refine ⟨after,fun p => ?_⟩
    change run gs ((front++p::rear)++[value g (front++p::rear)])=_
    simpa only [eqv,List.append_assoc,List.cons_append] using ha p

/-- Physical unique-read factorization for arbitrary input index (length
of front), any gate operation, arbitrary suffix fanout and the default-false
wire convention, including out-of-range companion/output. -/
theorem one_reader (pre post : List Gate) (front rear : List Bool) (op : GateOp) (k out : Nat)
    (kOther : k≠front.length) (outOther : out≠front.length)
    (noPre : ∀ g∈pre, front.length∉g.inputs)
    (noPost : ∀ g∈post, front.length∉g.inputs) :
    ∃ b : Bool, ∃ tail : Bool→Bool, ∀ p : Bool,
      (⟨pre++⟨op,[front.length,k]⟩::post,out⟩ : Circuit).eval (front++p::rear)=tail (op.eval [p,b]) := by
  classical
  obtain ⟨after,apre⟩ := scanWithout pre front rear noPre
  let b := (front++false::after).getD k false
  let tail (h : Bool) := (run post (front++false::(after++[h]))).getD out false
  refine ⟨b,tail,?_⟩
  intro p
  let g : Gate := ⟨op,[front.length,k]⟩
  have read : value g (front++p::after)=op.eval [p,b] := by
    simp only [value,g,List.map_cons,List.map_nil,pivot_index]
    rw [other_index front after p false k kOther]
  change (run (pre++g::post) (front++p::rear)).getD out false=_
  have split : run (pre++g::post) (front++p::rear)=
      run post ((run pre (front++p::rear))++[value g (run pre (front++p::rear))]) := by
    simp [run,List.foldl_append]
  rw [split,apre,read]
  obtain ⟨final,hpost⟩ := scanWithout post front (after++[op.eval [p,b]]) noPost
  unfold tail
  simp only [List.append_assoc,List.cons_append]
  rw [hpost p,hpost false]
  exact other_index front final p false out outOther

#print axioms CoOnlyReadPhysical.one_reader
end CoOnlyReadPhysical
