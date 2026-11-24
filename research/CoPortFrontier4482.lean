import PEqualNP.CoPortEdgeRows4482
import PEqualNP.CoPortPermutations4482
import PEqualNP.CoPortMoves4482

namespace CoPortFrontier4482
open CoPortRoots4482 CoPortTrace4482 CoPortCut4482 CoPortEdgeRows4482 CoBitBlock4482

def Reach (k : Nat) (xs : List W) := ∃ j≤k, Path join (cleanCut model label 6) j xs.toFinset

def eraseIf (xs : List W) (v : W) (drop : Bool) : List W :=
  if drop then xs.filter (fun w => w != v) else xs

def successor (xs : List W) (op : Bool) (a b : W) (da db : Bool) : List W :=
  join op a b :: eraseIf (eraseIf xs a da) b db

theorem set_eraseIf (xs : List W) (v : W) (d : Bool) :
    (eraseIf xs v d).toFinset=CoPortTrace4482.discard xs.toFinset v d := by
  cases d
  · rfl
  · ext w
    simp [eraseIf,CoPortTrace4482.discard,and_comm]

theorem set_successor (xs : List W) (op : Bool) (a b : W) (da db : Bool) :
    (successor xs op a b da db).toFinset =
      insert (join op a b) (CoPortTrace4482.discard (CoPortTrace4482.discard xs.toFinset a da) b db) := by
  simp only [successor,List.toFinset_cons,set_eraseIf]

theorem reach_width {xs k} (p : Reach k xs) : xs.toFinset.card ≤ 6+k := by
  obtain ⟨j,hj,h⟩ := p
  have bound := width (fun T (st : cleanCut model label 6 T) => st.1) h
  omega

theorem tight_exact {xs k} (h : xs.toFinset.card=6+k) (p : Reach k xs) :
    Path join (cleanCut model label 6) k xs.toFinset := by
  obtain ⟨j,hj,run⟩ := p
  have bound := width (fun T (st : cleanCut model label 6 T) => st.1) run
  have eq : j=k := by omega
  exact eq ▸ run

theorem children {xs k} (room : 6<xs.toFinset.card) (p : Reach (k+1) xs) :
    ∃ a∈xs, ∃ b∈xs, ∃ d da db : Bool,
      a≠b ∧ join d a b∉xs ∧ Reach k (successor xs d a b da db) := by
  obtain ⟨j,lo,run⟩ := p
  cases j with
  | zero =>
    cases run with
    | final _ st => exact False.elim ((Nat.not_le_of_gt room) st.1)
  | succ j =>
    obtain ⟨d,a,b,da,db,ma,mb,ne,fresh,sub⟩ := transition run
    exact ⟨a,List.mem_toFinset.mp ma,b,List.mem_toFinset.mp mb,d,da,db,ne,
      fun m => fresh (List.mem_toFinset.mpr m),j,by omega,by rwa [set_successor]⟩

def cov : List Mark → Bits
  | [] => 0
  | m::ms => (m.1 ^^^ m.2) ||| cov ms

theorem cov_member {ms : List Mark} {m : Mark} (i : Row) (mem : m∈ms)
    (on : (m.1 ^^^ m.2).getLsbD i.val=true) : (cov ms).getLsbD i.val=true := by
  induction ms with
  | nil => simp at mem
  | cons a t ih =>
    simp only [cov,BitVec.getLsbD_or,Bool.or_eq_true]
    rcases List.mem_cons.mp mem with rfl|inTail
    · exact Or.inl on
    · exact Or.inr (ih inTail)

theorem covered {xs k} (p : Reach k xs) : cov (xs.map mark)=BitVec.allOnes 258 := by
  obtain ⟨j,hj,path⟩ := p
  have sep := separated cell label model.applyJoin (fun T (t : cleanCut model label 6 T) => t.2.1) path
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  let i : Row := ⟨t,ht⟩
  have diff : label (lower i)≠label (upper i) := by rw [(labels i).1,(labels i).2]; decide
  obtain ⟨w,hw,ne⟩ := sep (lower i) (upper i) diff
  simp only [BitVec.getLsbD_allOnes,ht,decide_true]
  apply cov_member i (List.mem_map.mpr ⟨w,List.mem_toFinset.mp hw,rfl⟩)
  rw [difference]
  exact bne_iff_ne.mpr ne.symm

theorem equivalent {xs ys : List W} {k k' : Nat} (hk : k≤k') (g : G)
    (image : xs.toFinset.image (reorder (rowEquiv g))=ys.toFinset) (p : Reach k xs) : Reach k' ys := by
  obtain ⟨j,hj,run⟩ := p
  exact ⟨j,hj.trans hk,image ▸ reorder_path (rowEquiv g) (respects_label g) run⟩

end CoPortFrontier4482
