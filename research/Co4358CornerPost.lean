import PEqualNP.Co4358MaskFast
import PEqualNP.Co4358FastCorners
namespace CoNum4358.Tiny.Corners
open CoAO3143

def limit (k : Nat) (cs : List K) := cs.length==k+1 && clash cs

theorem limit_no {k : Nat} {cs : List K} (nd : cs.Nodup)
    (h : Live k 0 (cs.map wide).toFinset) : limit k cs=false := by
  apply Bool.eq_false_iff.mpr
  intro bad
  simp only [limit,Bool.and_eq_true,beq_iff_eq] at bad
  have n := List.toFinset_card_of_nodup (nd.map wide_inj)
  rw [List.length_map] at n
  exact Bool.false_ne_true ((clash_no h (by omega)).symm.trans bad.2)

def post (k q : Nat) (T : Table) (ws : List W) :=
  cap ws true && cap ws false &&
    (if k==0 then ws.any isGoal else !(limit k (ws.map Prod.fst) || matched T q ws))

theorem sound : MaskFast.SoundPost post := by
  intro k q T ws v nd h
  have old := Fast.finish_yes v nd h
  have loc := good_of h
  have live : Live k 0 ((ws.map Prod.fst).map wide).toFinset := by
    have E : ((ws.map Prod.fst).map wide).toFinset=ws.toFinset.image (fun w=>wide w.1) := by ext; simp
    rw [E]; exact loc.live
  unfold Fast.finish at old
  unfold post
  by_cases z : k=0
  · simpa [z] using old
  · have a := limit_no nd live
    have b := no_rect nd live
    simpa [z,a,b] using old

def node := MaskFast.nodeWith post
theorem node_ok {k q T ws} (v : Valid k T) (yes : node k q T ws=true) : ¬Trace (k+1) q ws.toFinset :=
  MaskFast.nodeWith_ok post sound v yes

end CoNum4358.Tiny.Corners
