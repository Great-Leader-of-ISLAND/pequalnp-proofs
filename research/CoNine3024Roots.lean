import PEqualNP.CoNine3024PaidState
import PEqualNP.CoNine3024Initial

namespace CoNine3024Roots
open CoNine3024 CoNine3024Rows CoNine3024PaidState
open CoAO3143Restriction CoAllRaw3024 CoThetaNine CoNine3024Initial

noncomputable section
local instance : DecidableEq (Wire Input) := Classical.decEq _

private theorem root_cases (p : Fin 11) (b : Bool) (w : Wire Input) :
    w∈((root p b).wires.map value).toFinset ↔
      (∃ i : Fin 9,w=vtx i) ∨ (b=true ∧ w=CoAllRaw3024.seed) ∨ (p.val≠10 ∧ w=inverse p) := by
  have raw : w∈(List.ofFn (rootAtom p)).map value ↔ ∃ i : Fin 9,w=vtx i := by
    constructor
    · intro h
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp h
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
      exact ⟨i,raw_value p i⟩
    · rintro ⟨i,rfl⟩
      exact List.mem_map.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,raw_value p i⟩
  change w∈(((List.ofFn (rootAtom p) ++ (if b then [seedAtom p] else [])) ++
      (if p.val=10 then [] else [inverseAtom p])).map value).toFinset ↔ _
  by_cases pn : p.val=10 <;> cases b <;>
    simp [pn,raw,List.map_append,List.mem_append,seed_value,inverse_value,or_assoc]

private theorem map_nd (ws : List Atom) (nd : (ws.map Atom.full).Nodup) : (ws.map value).Nodup := by
  induction ws with
  | nil => simp
  | cons a as ih =>
    obtain ⟨nf,tail⟩ := List.nodup_cons.mp nd
    refine List.nodup_cons.mpr ⟨?_,ih tail⟩
    intro hit
    obtain ⟨t,ht,eq⟩ := List.mem_map.mp hit
    exact nf (List.mem_map.mpr ⟨t,ht,full_inj eq⟩)

set_option maxRecDepth 8192 in
private theorem words_unique : ∀ (p : Fin 11) (b : Bool), ((root p b).wires.map Atom.full).Nodup := by decide +kernel

theorem root_unique (p : Fin 11) (b : Bool) : ((root p b).wires.map value).Nodup :=
  map_nd _ (words_unique p b)

theorem root_sound (p : Fin 11) (b : Bool) : ∀a∈(root p b).wires,Good p a := by
  intro a ha
  rcases List.mem_append.mp ha with old|neg
  · rcases List.mem_append.mp old with r|sd
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp r
      exact root_good _ _
    · cases b with
      | false => simp at sd
      | true =>
        obtain rfl : a=seedAtom p := by simpa using sd
        exact seed_good p
  · by_cases e : p.val=10
    · simp [e] at neg
    · obtain rfl : a=inverseAtom p := by simpa [e] using neg
      exact inverse_good p

theorem select_root (L : SignedLower) (p : Fin 11) {k S} (small : k≤13)
    (c : CoClean3024.Clean ans k S) (lab : ∀ w∈S,∃ j,w=label p j) (raw : ∀ i : Fin 9,vtx i∈S) :
    ∃ q : Fin 11, ∃ b : Bool, (b=true ∨ q=9) ∧ ((root q b).wires.map value).toFinset=S := by
  classical
  have required := must_use_seed L p small c lab
  by_cases uses : inverse p∈S
  · have neq : p.val≠10 := by
      intro ten
      exact CoClean3024.inputs_vary c ans_varies _ uses
        ⟨true,by simp [inverse,ten]⟩
    refine ⟨p,decide (CoAllRaw3024.seed∈S),?_,?_⟩
    · rcases required with sd|⟨hp,_⟩
      · exact Or.inl (decide_eq_true sd)
      · exact Or.inr hp
    ext w
    rw [root_cases]
    simp only [decide_eq_true_eq]
    constructor
    · rintro (⟨i,rfl⟩|⟨sd,rfl⟩|⟨_,rfl⟩)
      · exact raw i
      · exact sd
      · exact uses
    · intro hw
      rcases options p c lab w hw with r|rfl|rfl
      · exact Or.inl r
      · exact Or.inr (Or.inl ⟨hw,rfl⟩)
      · exact Or.inr (Or.inr ⟨neq,rfl⟩)
  · have sd : CoAllRaw3024.seed∈S := required.resolve_right (fun h => uses h.2)
    refine ⟨10,true,Or.inl rfl,?_⟩
    ext w
    rw [root_cases]
    simp only [show (10 : Fin 11).val=10 from rfl,ne_self_eq_false,false_and,or_false,true_and]
    constructor
    · rintro (⟨i,rfl⟩|rfl)
      · exact raw i
      · exact sd
    · intro hw
      rcases options p c lab w hw with r|rfl|rfl
      · exact Or.inl r
      · exact Or.inr rfl
      · exact (uses hw).elim

#print axioms CoNine3024Roots.select_root
end
end CoNine3024Roots
