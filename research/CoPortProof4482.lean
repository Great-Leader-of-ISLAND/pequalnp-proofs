import PEqualNP.CoPortBanks4482
namespace CoPortProof4482
open CoPortEngine4482 CoPortSlice4482 CoPortRows4482 CoPortBanks4482
open PEqualNP.CircuitLowerBounds CoSwitch3302.MonotoneWires3302
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem all_cases (i : Fin 126) : verified i = true := by
  fin_cases i <;> decide +kernel

theorem one_computed (b : Fin 512) (five : pop b.val=5) (gs : List Gate)
    (len : gs.length≤7) (legal : ∀ g∈gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (z : Nat) : ∃ x y : Input, graph x ≠ graph y ∧ sameOn b.val x y ∧
      value (whole gs) x z = value (whole gs) y z := by
  obtain ⟨j,e⟩ := present b five
  have h := all_cases j
  simp only [verified,Bool.and_eq_true,decide_eq_true_eq] at h
  have rv := rows h.1.1
  have no := no_decision (entry j).1 (entry j).2 h.1.2 h.2
    (fun i => (rv i).1) (fun i => (rv i).2) gs len legal z
  rw [e] at no
  by_contra bad
  apply no
  intro x y seen eq
  by_contra ne
  exact bad ⟨x,y,ne,seen,eq⟩

def widened : Array (Fin 512) := #[31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,47,47,47,47,47,47,47,47,47,47,47,47,47,47,47,47,55,55,55,55,55,55,55,55,59,59,59,59,61,61,62,63,79,79,79,79,79,79,79,79,79,79,79,79,79,79,79,79,87,87,87,87,87,87,87,87,91,91,91,91,93,93,94,95,103,103,103,103,103,103,103,103,107,107,107,107,109,109,110,111,115,115,115,115,117,117,118,119,121,121,122,123,124,125,126,127,143,143,143,143,143,143,143,143,143,143,143,143,143,143,143,143,151,151,151,151,151,151,151,151,155,155,155,155,157,157,158,159,167,167,167,167,167,167,167,167,171,171,171,171,173,173,174,175,179,179,179,179,181,181,182,183,185,185,186,187,188,189,190,191,199,199,199,199,199,199,199,199,203,203,203,203,205,205,206,207,211,211,211,211,213,213,214,215,217,217,218,219,220,221,222,223,227,227,227,227,229,229,230,231,233,233,234,235,236,237,238,239,241,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,271,271,271,271,271,271,271,271,271,271,271,271,271,271,271,271,279,279,279,279,279,279,279,279,283,283,283,283,285,285,286,287,295,295,295,295,295,295,295,295,299,299,299,299,301,301,302,303,307,307,307,307,309,309,310,311,313,313,314,315,316,317,318,319,327,327,327,327,327,327,327,327,331,331,331,331,333,333,334,335,339,339,339,339,341,341,342,343,345,345,346,347,348,349,350,351,355,355,355,355,357,357,358,359,361,361,362,363,364,365,366,367,369,369,370,371,372,373,374,375,376,377,378,379,380,381,382,383,391,391,391,391,391,391,391,391,395,395,395,395,397,397,398,399,403,403,403,403,405,405,406,407,409,409,410,411,412,413,414,415,419,419,419,419,421,421,422,423,425,425,426,427,428,429,430,431,433,433,434,435,436,437,438,439,440,441,442,443,444,445,446,447,451,451,451,451,453,453,454,455,457,457,458,459,460,461,462,463,465,465,466,467,468,469,470,471,472,473,474,475,476,477,478,479,481,481,482,483,484,485,486,487,488,489,490,491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511]

def extendMask (b : Fin 512) : Fin 512 := widened[b.val]'(by
  have h : widened.size=512 := by decide +kernel
  omega)

theorem extension : ∀ b : Fin 512, pop b.val≤5 → pop (extendMask b).val=5 ∧
    ∀ i : Fin 9, b.val.testBit i.val=true → (extendMask b).val.testBit i.val=true := by decide +kernel

theorem at_most_five (b : Fin 512) (small : pop b.val≤5) (gs : List Gate)
    (len : gs.length≤7) (legal : ∀ g∈gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (z : Nat) : ∃ x y : Input, graph x ≠ graph y ∧ sameOn b.val x y ∧
      value (whole gs) x z = value (whole gs) y z := by
  obtain ⟨sz,more⟩ := extension b small
  obtain ⟨x,y,ne,s,e⟩ := one_computed (extendMask b) sz gs len legal z
  exact ⟨x,y,ne,fun i h => s i (more i h),e⟩

theorem wire_observations {ports : Finset Nat} (b : Fin 512) (small : pop b.val≤5)
    (gs : List Gate) (len : gs.length≤7)
    (legal : ∀ g∈gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) (z : Nat)
    (covered : ∀ u∈ports, u=z ∨ ∃ j : Fin 9, u=j.val ∧ b.val.testBit j.val=true) :
    ∃ x y : Input, graph x≠graph y ∧ ∀u∈ports,
      ((whole gs).wires (List.ofFn x)).getD u false = ((whole gs).wires (List.ofFn y)).getD u false := by
  obtain ⟨x,y,ne,seen,e⟩ := at_most_five b small gs len legal z
  refine ⟨x,y,ne,?_⟩
  intro u hu
  rcases covered u hu with rfl|⟨j,rfl,on⟩
  · exact e
  · change value _ x j = value _ y j
    simpa only [input_value] using seen j on

#print axioms wire_observations

#print axioms one_computed
end CoPortProof4482
