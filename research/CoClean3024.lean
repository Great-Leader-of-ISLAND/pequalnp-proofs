import PEqualNP.CoAO3143Restriction

namespace CoClean3024
open CoAO3143Restriction PEqualNP.CircuitLowerBounds

noncomputable section
local instance {α : Type} : DecidableEq (Wire α) := Classical.decEq _

inductive Clean {α : Type} (out : Wire α) : Nat → Finset (Wire α) → Prop
  | stop : Clean out 0 {out}
  | gate {k : Nat} {U : Finset (Wire α)} (d : Bool) (a b : Wire α)
      (ne : a≠b) (nonconstant : ¬Constant (op d a b))
      (left : op d a b≠a) (right : op d a b≠b) (fresh : op d a b∉U)
      (tail : Clean out k (insert (op d a b) U)) : Clean out (k+1) (insert a (insert b U))

theorem toCone {α : Type} {out : Wire α} {k S} (c : Clean out k S) : Cone out k S := by
  induction c with
  | stop => exact Cone.stop
  | gate d a b ne nonconstant left right fresh tail ih => exact Cone.gate d a b fresh ih

theorem inputs_vary {α : Type} {out : Wire α} {k S} (c : Clean out k S)
    (output : ¬Constant out) : ∀ w∈S, ¬Constant w := by
  induction c with
  | stop => simpa using output
  | @gate k U d a b ne nc left right fresh tail ih =>
    intro w hw hc
    rcases Finset.mem_insert.mp hw with rfl|hm
    · obtain ⟨v,rfl⟩ := hc
      cases d <;> cases v
      · exact nc ⟨false,by funext r; simp [op,con]⟩
      · exact right (by funext r; simp [op,con])
      · exact right (by funext r; simp [op,con])
      · exact nc ⟨true,by funext r; simp [op,con]⟩
    rcases Finset.mem_insert.mp hm with rfl|old
    · obtain ⟨v,rfl⟩ := hc
      cases d <;> cases v
      · exact nc ⟨false,by funext r; simp [op,con]⟩
      · exact left (by funext r; simp [op,con])
      · exact left (by funext r; simp [op,con])
      · exact nc ⟨true,by funext r; simp [op,con]⟩
    exact ih w (Finset.mem_insert_of_mem old) hc

private theorem fetch {α : Type} (ws : List (Wire α)) (i : Nat) :
    ws.getD i (con false)∈ws ∨ Constant (ws.getD i (con false)) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : ws[i]? with
  | none => exact Or.inr ⟨false,rfl⟩
  | some a => exact Or.inl (List.mem_of_getElem? h)

private theorem classify {α : Type} (ws : List (Wire α)) (g : Gate)
    (legal : (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) :
    Constant (readGate ws g) ∨ ∃ d a b, (a ∈ ws ∨ Constant a) ∧ (b ∈ ws ∨ Constant b) ∧
      readGate ws g=op d a b := by
  rcases g with ⟨kind,ins⟩
  obtain ⟨hk,hlen⟩ := legal
  change kind=.and ∨ kind=.or at hk
  change ins.length≤2 at hlen
  cases ins with
  | nil =>
    left
    rcases hk with rfl|rfl
    · exact ⟨true,rfl⟩
    · exact ⟨false,rfl⟩
  | cons i is =>
    cases is with
    | nil =>
      right
      rcases hk with rfl|rfl
      · exact ⟨false,_,_,fetch ws i,fetch ws i,by funext x; simp [readGate,GateOp.eval,op]⟩
      · exact ⟨true,_,_,fetch ws i,fetch ws i,by funext x; simp [readGate,GateOp.eval,op]⟩
    | cons j js =>
      cases js with
      | nil =>
        right
        rcases hk with rfl|rfl
        · exact ⟨false,_,_,fetch ws i,fetch ws j,by funext x; simp [readGate,GateOp.eval,op]⟩
        · exact ⟨true,_,_,fetch ws i,fetch ws j,by funext x; simp [readGate,GateOp.eval,op]⟩
      | cons k ks => simp at hlen

theorem extract {α : Type} (out : Wire α) (gs : List Gate) (ws : List (Wire α))
    (legal : ∀ g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (hit : out∈circuitWires gs ws ∨ Constant out) :
    ∃ k S, k≤gs.length ∧ Clean out k S ∧ ∀ a∈S, a∈ws ∨ Constant a := by
  classical
  induction gs generalizing ws with
  | nil => exact ⟨0,{out},by simp,Clean.stop,by simpa [circuitWires] using hit⟩
  | cons g gs ih =>
    let z := readGate ws g
    obtain ⟨k,S,bound,tail,src⟩ := ih (ws++[z]) (fun a ha => legal a (List.mem_cons_of_mem _ ha)) hit
    by_cases use : z ∈ S
    · by_cases fixed : z ∈ ws ∨ Constant z
      · refine ⟨k,S,by simp; omega,tail,?_⟩
        intro w hw
        rcases src w hw with hh | hc
        · rcases List.mem_append.mp hh with old|last
          · exact Or.inl old
          · rw [List.mem_singleton.mp last]
            exact fixed
        · exact Or.inr hc
      · rcases classify ws g (legal g List.mem_cons_self) with constant | ⟨d,a,b,ha,hb,e⟩
        · exact (fixed (Or.inr constant)).elim
        let U := S.erase z
        have eq : z=op d a b := e
        have fresh : op d a b∉U := by simp [U,←eq]
        have next : Clean out k (insert (op d a b) U) := by simpa [U,←eq,Finset.insert_erase use] using tail
        have notC : ¬Constant (op d a b) := fun hc => fixed (Or.inr (eq.symm ▸ hc))
        have left : op d a b ≠ a := fun ea => fixed ((eq.trans ea).symm ▸ ha)
        have right : op d a b ≠ b := fun eb => fixed ((eq.trans eb).symm ▸ hb)
        have diff : a≠b := by
          rintro rfl
          apply left
          funext r
          cases d <;> simp [op]
        refine ⟨k+1,_,by simpa using bound,Clean.gate d a b diff notC left right fresh next,?_⟩
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact ha
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact hb
        obtain ⟨ne,hs⟩ := Finset.mem_erase.mp hw
        rcases src w hs with hh | hc
        · rcases List.mem_append.mp hh with old|last
          · exact Or.inl old
          · exact (ne (List.mem_singleton.mp last)).elim
        · exact Or.inr hc
    · refine ⟨k,S,by simp; omega,tail,?_⟩
      intro w hw
      rcases src w hw with hh | hc
      · rcases List.mem_append.mp hh with old|last
        · exact Or.inl old
        · exact (use ((List.mem_singleton.mp last) ▸ hw)).elim
      · exact Or.inr hc

#print axioms CoClean3024.extract
end
end CoClean3024
