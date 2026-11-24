import PEqualNP.Co1677ThirdReader
import PEqualNP.Co1677Restriction

namespace Co1677Or26
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CoCommute1675 Co1675ShardFour (graph)
open Co1677ThirdReader (sample read_gate exists_extra)
open PEqualNP.Research.PetersenRestrict

private theorem raw_pair (a b : Nat) (diff : ∀ k : Fin 9,k.val≠6 → sample a k=sample b k)
    (i : Nat) (ne : i≠6) : (List.ofFn (sample a)).getD i false=(List.ofFn (sample b)).getD i false := by
  by_cases h : i<9
  · let k : Fin 9 := ⟨i,h⟩
    simpa [List.getD_eq_getElem?_getD,List.getElem?_ofFn,h,k] using diff k ne
  · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]

theorem heads (a b : Gate) (tail : List Gate) (out : Nat)
    (one : ∀ x : Fin 9 → Bool,((Circuit.mk (a::b::tail) out).wires (List.ofFn x)).getD 9 false=(x 0 || x 6))
    (two : ∀ x : Fin 9 → Bool,((Circuit.mk (a::b::tail) out).wires (List.ofFn x)).getD 10 false=(x 2 || x 6)) :
    6∈pins a ∧ 6∈pins b := by
  have first (m : Nat) := (prefixReads a b tail out (sample m)).1.symm.trans (one (sample m))
  have next (m : Nat) := (prefixReads a b tail out (sample m)).2.symm.trans (two (sample m))
  constructor
  · by_contra no
    have eq := read_gate a _ _ no (raw_pair 0 64 (by decide +kernel))
    rw [first,first] at eq
    exact Bool.noConfusion (show false=true from eq)
  · by_contra no
    have same : ∀ i,i≠6 → ((List.ofFn (sample 1))++[true]).getD i false=
          ((List.ofFn (sample 65))++[true]).getD i false := by
      intro i hi
      simp only [read_snoc,List.length_ofFn,raw_pair 1 65 (by decide +kernel) i hi]
    have eq := read_gate b _ _ no same
    have l := next 1
    have r := next 65
    rw [first] at l r
    change _=false at l
    change _=true at r
    exact Bool.noConfusion ((l.symm.trans eq).trans r)

private theorem counted (g : Gate) (hit : 6∈pins g) :
    (pins g).toFinset ∩ ({6} : Finset Nat)≠∅ := by
  exact Finset.ne_empty_of_mem (show 6 ∈ (pins g).toFinset ∩ ({6} : Finset Nat) from (Finset.mem_inter.mpr ⟨by simpa using hit,by simp⟩))

private theorem positive (gs : List Gate) (h : ∃ g∈gs,6∈pins g) : 1≤directSavings {6} gs := by
  induction gs with
  | nil => simp at h
  | cons a gs ih =>
    obtain ⟨g,hg,hit⟩ := h
    rcases List.mem_cons.mp hg with eq|rest
    · subst g
      simp [directSavings,counted a hit]
    · have := ih ⟨g,rest,hit⟩
      unfold directSavings
      split <;> omega

def seed : List Wire := [.port 0,.port 1,.port 2,.port 3,.port 4,.port 5,.fixed false,.port 6,.port 7]
def liftRow (x : Fin 8 → Bool) : Fin 9 → Bool := ![x 0,x 1,x 2,x 3,x 4,x 5,false,x 6,x 7]
def minor (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 5 && x 6) || (x 7 && x 5)
private theorem minor_eq (x : Fin 8 → Bool) : graph (liftRow x)=minor x := by
  change (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && false || x 2 && x 6 || x 3 && x 7 || x 5 && x 6 || false && x 7 || x 7 && x 5)=_
  simp [minor]

theorem or26 (lower : ∀ D : Circuit,FanInTwo D → circuitFun 8 D=minor → 13≤D.size)
    (a b : Gate) (tail : List Gate) (out : Nat) (fan : FanInTwo ⟨a::b::tail,out⟩)
    (one : ∀ x : Fin 9 → Bool,((Circuit.mk (a::b::tail) out).wires (List.ofFn x)).getD 9 false=(x 0 || x 6))
    (two : ∀ x : Fin 9 → Bool,((Circuit.mk (a::b::tail) out).wires (List.ofFn x)).getD 10 false=(x 2 || x 6))
    (solves : circuitFun 9 ⟨a::b::tail,out⟩=graph) : 16≤(Circuit.mk (a::b::tail) out).size := by
  let C : Circuit := ⟨a::b::tail,out⟩
  have changed (x : Fin 8 → Bool) : C.eval (substituted seed x)=minor x := by
    change C.eval (List.ofFn (liftRow x))=minor x
    exact (congrFun solves (liftRow x)).trans (minor_eq x)
  have real : ∃ x y : Fin 8 → Bool,C.eval (substituted seed x)≠C.eval (substituted seed y) := by
    refine ⟨fun _ => false,fun _ => true,?_⟩
    rw [changed,changed]
    decide
  have price := charge C fan seed (n:=8) (by intro p hp;simp [seed] at hp;rcases hp with h|h|h|h|h|h|h|h|h <;> subst p <;> decide)
        real 13 (fun D hd eq => lower D hd (funext fun x => (eq x).trans (changed x)))
  have ready : Ready {6} seed := by
    intro i hi
    have eq : i=6 := by simpa using hi
    subst i
    exact ⟨by decide, false,rfl⟩
  have book := scan_direct {6} C.gates 8 seed ready
  obtain ⟨ra,rb⟩ := heads a b tail out one two
  have third := positive tail (exists_extra a b tail out one two solves)
  change directSavings {6} (a::b::tail)≤_ at book
  simp only [directSavings,if_neg (counted a ra),if_neg (counted b rb)] at book
  change 16≤C.size
  omega

#print axioms or26
end Co1677Or26
