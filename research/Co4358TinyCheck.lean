import PEqualNP.Co4358TinyModel
import PEqualNP.Co4358TinyRect

namespace CoNum4358.Tiny
open CoAO3143
set_option maxRecDepth 10000

structure Table where
  count : Nat
  row : Nat → Nat × List W
  loc : Nat → List W → Nat

def Valid (k : Nat) (T : Table) := ∀ i<T.count, ¬Trace k (T.row i).1 (T.row i).2.toFinset

def matched (T : Table) (q : Nat) (ws : List W) :=
  let i := T.loc q ws
  let r := T.row i
  decide (i<T.count) && r.1==q && ws.isPerm r.2

theorem matched_false {k T q ws} (v : Valid k T) (h : Trace k q ws.toFinset) :
    matched T q ws=false := by
  apply Bool.eq_false_iff.mpr
  intro bad
  simp only [matched,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,List.isPerm_iff] at bad
  obtain ⟨⟨idx,qeq⟩,perm⟩ := bad
  have eqs : ws.toFinset=(T.row (T.loc q ws)).2.toFinset := by
    ext t; simpa using perm.mem_iff (a:=t)
  exact v _ idx (by rwa [qeq,←eqs])

theorem good_of {k q S} (run : Trace k q S) : Good k S := by
  cases run with
  | done q w orig c₀ c₃ =>
    constructor
    · rw [Finset.image_singleton,orig,target_value]
      exact Live.stop
    · intro s; exact ⟨w,Finset.mem_singleton_self _,by cases s <;> assumption⟩
  | step _ _ _ _ _ _ _ _ facts _ => exact facts

def cap (ws : List W) (s : Bool) := ws.any fun w => capability s w.2
def isGoal (w : W) := w.1==255 && w.2.1.separates && w.2.2.separates
private theorem goal_of {q S} (h : Trace 0 q S) : ∃u∈S,isGoal u=true := by
  cases h with
  | done q w o a b => exact ⟨w,Finset.mem_singleton_self _,by simp [isGoal,o,a,b]⟩

def overfull (k : Nat) (cs : List K) := decide (k+1<cs.length)
def rectBound (k : Nat) (cs : List K) := (cs.length==k+1) && restrict cs

theorem no_over {k : Nat} {cs : List K} (nd₀ : cs.Nodup) (h : Live k 0 (cs.map wide).toFinset) : overfull k cs=false := by
  apply Bool.eq_false_iff.mpr
  intro bad
  simp only [overfull,Bool.and_eq_true,decide_eq_true_eq] at bad
  have nd : (cs.map wide).Nodup := nd₀.map wide_inj
  have eq := List.toFinset_card_of_nodup nd
  rw [List.length_map] at eq
  have width := ProtocolProof.width h
  omega

theorem no_rect {k : Nat} {cs : List K} (nd₀ : cs.Nodup) (h : Live k 0 (cs.map wide).toFinset) : rectBound k cs=false := by
  apply Bool.eq_false_iff.mpr
  intro bad
  simp only [rectBound,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at bad
  have nd : (cs.map wide).Nodup := nd₀.map wide_inj
  have eq := List.toFinset_card_of_nodup nd
  rw [List.length_map] at eq
  exact Bool.false_ne_true ((restrict_false h (by omega)).symm.trans bad.2)

def blocked (k q : Nat) (T : Table) (ws : List W) : Bool :=
  let cs := ws.map Prod.fst
  !(cap ws true && cap ws false) || overfull k cs || missing cs ||
    (if k==0 then !(ws.any isGoal) else rectBound k cs || matched T q ws)

theorem blocked_false {k q T ws} (v : Valid k T) (nd : (ws.map Prod.fst).Nodup) (run : Trace k q ws.toFinset) :
    blocked k q T ws=false := by
  have f := good_of run
  have both (s : Bool) : cap ws s=true := by
    obtain ⟨x,hx,ok⟩ := f.caps s
    exact List.any_eq_true.mpr ⟨x,List.mem_toFinset.mp hx,ok⟩
  let cs := ws.map Prod.fst
  have same : (cs.map wide).toFinset=ws.toFinset.image (fun w => wide w.1) := by
    ext x; simp [cs]
  have orig : Live k 0 (cs.map wide).toFinset := by rw [same]; exact f.live
  change (!(cap ws true && cap ws false) || overfull k cs || missing cs ||
    (if k==0 then !(ws.any isGoal) else rectBound k cs || matched T q ws))=false
  rw [both,both,no_over nd orig,missing_false orig]
  by_cases eq : k=0
  · subst k
    obtain ⟨w,owns,yes⟩ := goal_of run
    have hit : ws.any isGoal=true := List.any_eq_true.mpr ⟨w,List.mem_toFinset.mp owns,yes⟩
    simp [hit]
  · have rr : rectBound k cs=false := no_rect nd orig
    simp [eq,matched_false v run,rr]

def remaining (ws : List W) (a b : W) (ka kb : Bool) :=
  ws.filter fun z => (z != a || ka) && (z != b || kb)

theorem remaining_set {ws : List W} {U : Finset W} {a b : W} (eq : ws.toFinset=insert a (insert b U)) :
    (remaining ws a b (decide (a∈U)) (decide (b∈U))).toFinset=U := by
  ext x
  have mem : x∈ws ↔ x=a ∨ x=b ∨ x∈U := by rw [←List.mem_toFinset,eq]; simp
  simp only [List.mem_toFinset,List.mem_filter,remaining,Bool.and_eq_true,Bool.or_eq_true,
    bne_iff_ne,decide_eq_true_eq,mem]
  by_cases xa : x=a <;> by_cases xb : x=b <;> subst_vars <;> aesop

def branch (k q : Nat) (T : Table) (ws : List W) (a b : W) (d : Bool) :=
  let z := make d a b
  decide (pay d a b≤q) && z.1 != 0 && z.1 != 32767 &&
    !(bare.contains z.1) && !(ws.any fun w => w.1==z.1) &&
      options.any fun ka => options.any fun kb =>
        !(blocked k (q-pay d a b) T (z::remaining ws a b ka kb))

def check (k q : Nat) (T : Table) (ws : List W) :=
  decide (ws.map Prod.fst).Nodup && !(scanPairs (fun a b => options.any (branch k q T ws a b)) ws)

theorem mcomm (d : Bool) (a b : W) : make d a b=make d b a := by
  cases d <;> simp [make,makeKW,mergePair,mergeFlag,BitVec.or_comm,BitVec.and_comm,Bool.or_comm,Bool.and_comm]

theorem pcomm (d : Bool) (a b : W) : pay d a b=pay d b a := by simp [pay,Bool.or_comm]

private theorem branch_found {k q T ws U d a b}
    (val : Valid k T) (hn : (ws.map Prod.fst).Nodup) (sub : ws.toFinset=insert a (insert b U))
    (bd : pay d a b≤q) (pr : (make d a b).1≠0 ∧ (make d a b).1≠32767)
    (nu : (make d a b).1∉ws.toFinset.image Prod.fst) (nr : (make d a b).1∉bare)
    (child : Trace k (q-pay d a b) (insert (make d a b) U)) :
    (options.any (branch k q T ws a b))=true := by
  apply List.any_eq_true.mpr
  refine ⟨d,all_options _,?_⟩
  have no : (ws.any fun w => w.1==(make d a b).1)=false := by
    apply Bool.eq_false_iff.mpr
    intro bad
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp bad
    exact nu (Finset.mem_image.mpr ⟨x,List.mem_toFinset.mpr hx,beq_iff_eq.mp he⟩)
  have en : (decide (pay d a b≤q) && (make d a b).1 != 0 && (make d a b).1 != 32767 &&
      !(bare.contains (make d a b).1) && !(ws.any fun w => w.1==(make d a b).1))=true := by
    simp [bd,nr,no]
    exact pr
  change (_ && options.any (fun ka => options.any (fun kb =>
    !(blocked k (q-pay d a b) T (make d a b::remaining ws a b ka kb)))))=true
  rw [en,Bool.true_and]
  apply List.any_eq_true.mpr
  refine ⟨decide (a∈U),all_options _,List.any_eq_true.mpr ⟨decide (b∈U),all_options _,?_⟩⟩
  have step : Trace k (q-pay d a b)
      ((make d a b)::remaining ws a b (decide (a∈U)) (decide (b∈U))).toFinset := by
    simpa [remaining_set sub] using child
  let r := remaining ws a b (decide (a∈U)) (decide (b∈U))
  have subr : r.Sublist ws := List.filter_sublist
  have nr₀ : (r.map Prod.fst).Nodup := hn.sublist (subr.map _)
  have new₀ : (make d a b).1∉r.map Prod.fst := by
    intro bad
    obtain ⟨x,hx,he⟩ := List.mem_map.mp bad
    exact nu (Finset.mem_image.mpr ⟨x,List.mem_toFinset.mpr (subr.subset hx),he⟩)
  have whole : (((make d a b)::r).map Prod.fst).Nodup := .cons new₀ nr₀
  exact congrArg Bool.not (blocked_false val whole step)

theorem check_ok {k q T ws} (v : Valid k T) (yes : check k q T ws=true) :
    ¬Trace (k+1) q ws.toFinset := by
  intro h
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at yes
  generalize eq : ws.toFinset = S at h
  cases h with
  | step d a b ne bd pr nu nr facts child =>
    have ha : a∈ws := by rw [←List.mem_toFinset,eq]; simp
    have hb : b∈ws := by rw [←List.mem_toFinset,eq]; simp
    have nu' : (make d a b).1∉ws.toFinset.image Prod.fst := by rwa [eq]
    have A := branch_found v yes.1 eq bd pr nu' nr child
    have B := branch_found (k:=k) (q:=q) (d:=d) v yes.1 (eq.trans (Finset.insert_comm _ _ _))
      (by rwa [pcomm d b a]) (by rwa [mcomm d b a]) (by rwa [mcomm d b a])
      (by rwa [mcomm d b a]) (by rwa [pcomm d b a,mcomm d b a])
    have same := scanPairs_complete (fun a b => options.any (branch k q T ws a b)) ha hb ne A B
    simpa [same] using yes.2

end CoNum4358.Tiny
