import PEqualNP.Defs

namespace CoNearReaders3825
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
noncomputable section

def atPos (C : Circuit) (k : ℕ) := NestedCover.gateAt C k

def direct (C : Circuit) (v : Fin 9) :=
  (Finset.range C.size).filter fun i => v.val ∈ (atPos C i).inputs

def special (C : Circuit) (v : Fin 9) : Finset ℕ := by
  classical
  exact (direct C v).filter fun i => (atPos C i).op = .and ∨ (atPos C i).op = .not

def near (C : Circuit) (v : Fin 9) : Finset ℕ := by
  classical
  exact (Finset.range C.size).filter fun i =>
    v.val ∈ (atPos C i).inputs ∨
      ∃ j < i, v.val ∈ (atPos C j).inputs ∧
        ((atPos C j).op = .and ∨ (atPos C j).op = .not) ∧ 9+j ∈ (atPos C i).inputs

def extra (C : Circuit) (v : Fin 9) := near C v \ direct C v

def physical (C : Circuit) (v : Fin 9) : Prop :=
  ∀ S : Finset ℕ,(∀ i∈S,i < C.size ∧ (v.val ∈ (atPos C i).inputs ∨
    ∃ j < i,v.val ∈ (atPos C j).inputs ∧
      ((atPos C j).op= .and ∨ (atPos C j).op= .not) ∧ 9+j ∈ (atPos C i).inputs)) → S.card≤3

theorem physical_iff (C : Circuit) (v : Fin 9) : physical C v ↔ (near C v).card≤3 := by
  classical
  constructor
  · intro h
    apply h (near C v)
    intro i hi
    obtain ⟨a,b⟩ := Finset.mem_filter.mp hi
    exact ⟨Finset.mem_range.mp a,b⟩
  · intro h S s
    apply (Finset.card_le_card ?_).trans h
    intro i hi
    obtain ⟨a,b⟩ := s i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr a,b⟩

theorem direct_sub (C : Circuit) (v : Fin 9) : direct C v ⊆ near C v := by
  classical
  intro j hj
  obtain ⟨a,b⟩ := Finset.mem_filter.mp hj
  exact Finset.mem_filter.mpr ⟨a,Or.inl b⟩

theorem count (C : Circuit) (v : Fin 9) (h : physical C v) :
    (extra C v).card + (direct C v).card ≤ 3 := by
  classical
  have sum := Finset.card_sdiff_add_card_eq_card (direct_sub C v)
  change (near C v \ direct C v).card + (direct C v).card ≤ 3
  rw [sum]
  exact (physical_iff C v).mp h

/-- The only structural input needed in the following counting consequences:
    each AND/NOT direct reader has a later user which does not read the raw vertex. -/
def escapes (C : Circuit) (v : Fin 9) : Prop :=
  ∀ j∈special C v,∃ i∈extra C v,j < i ∧ 9+j∈(atPos C i).inputs

theorem three (C : Circuit) (v : Fin 9) (h : physical C v) (live : escapes C v)
    (num : (direct C v).card=3) : special C v=∅ := by
  classical
  have cap := count C v h
  have no : (extra C v).card=0 := by omega
  have gone := Finset.card_eq_zero.mp no
  apply le_antisymm ?_ (Finset.empty_subset _)
  intro j hj
  obtain ⟨i,hi,_⟩ := live j hj
  exact (Finset.notMem_empty i (gone ▸ hi)).elim

theorem two (C : Circuit) (v : Fin 9) (h : physical C v) (live : escapes C v)
    (num : (direct C v).card=2) (has : (special C v).Nonempty) :
    ∃ i,extra C v={i} ∧ ∀ j∈special C v,j < i ∧ 9+j∈(atPos C i).inputs := by
  classical
  obtain ⟨j,hj⟩ := has
  obtain ⟨i,hi,_⟩ := live j hj
  have cap := count C v h
  have atMost : (extra C v).card≤1 := by omega
  have unique (k) (hk : k∈extra C v) : k=i := Finset.card_le_one_iff.mp atMost hk hi
  refine ⟨i,?_,?_⟩
  · ext k
    constructor
    · exact fun hk => Finset.mem_singleton.mpr (unique k hk)
    · intro hk
      simpa [Finset.mem_singleton.mp hk] using hi
  · intro u hu
    obtain ⟨k,hk,horder,hwire⟩ := live u hu
    simpa [unique k hk] using And.intro horder hwire

/-- A direct raw co-reader with a previous AND(x,b), respectively NOT(x),
    always returns an existing wire, respectively a constant. -/
theorem absorption (v b : Bool) :
    (v && (v && b)) = (v && b) ∧ (v || (v && b))=v ∧
    (v && !v)=false ∧ (v || !v)=true := by cases v <;> cases b <;> decide

end
end CoNearReaders3825
