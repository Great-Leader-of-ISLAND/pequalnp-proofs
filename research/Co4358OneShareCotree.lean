import PEqualNP.Co4358OneShareProduct

namespace CoAO3143.OneShare
open ProtocolProof
open Cotree (leftChoice)

def Together (e : F) (z : Sig) (side : Bool) (a b : Sig) : Prop :=
  ∃ fixed i j : Row,
    (if side then e.pick z fixed i else e.pick z i fixed)=some a ∧
    (if side then e.pick z fixed j else e.pick z j fixed)=some b

def Connected (rel : Sig → Sig → Prop) (X : Finset Sig) :=
  ∀ f : Sig→Bool, (∀a∈X,∀b∈X,rel a b→f a=f b) → ∀a∈X,∀b∈X,f a=f b

private theorem at_side {l r : F} (dis : l.vars.Disjoint r.vars) (s : Sig) (d : Bool) {a p n}
    (hit : (F.fork d l r).pick s p n=some a) :
    decide (a∈l.vars)=leftChoice d (l.val s) p n := by
  cases side : leftChoice d (l.val s) p n
  · have h : r.pick s p n=some a := by simpa only [F.pick,side,Bool.false_eq_true,↓reduceIte] using hit
    have na : a∉l.vars := fun mem => List.disjoint_left.mp dis mem (pick_mem _ _ _ _ h)
    simp [na]
  · have h : l.pick s p n=some a := by simpa only [F.pick,side,↓reduceIte] using hit
    simp [pick_mem _ _ _ _ h]

private theorem left_hit {l r : F} {d : Bool} {s a p n} (dis : l.vars.Disjoint r.vars) (mem : a∈l.vars)
    (hit : (F.fork d l r).pick s p n=some a) : l.pick s p n=some a := by
  have active := at_side dis s d hit
  have dir : leftChoice d (l.val s) p n=true := by simpa [mem] using active.symm
  simpa only [F.pick,dir,↓reduceIte] using hit

private theorem right_hit {l r : F} {d : Bool} {s a p n} (dis : l.vars.Disjoint r.vars) (mem : a∈r.vars)
    (hit : (F.fork d l r).pick s p n=some a) : r.pick s p n=some a := by
  have no : a∉l.vars := fun h => List.disjoint_left.mp dis h mem
  have active := at_side dis s d hit
  have dir : leftChoice d (l.val s) p n=false := by simpa [no] using active.symm
  simpa only [F.pick,dir,Bool.false_eq_true,↓reduceIte] using hit

private theorem descendL {l r : F} {d u : Bool} {s a b} (dis : l.vars.Disjoint r.vars)
    (ha : a∈l.vars) (hb : b∈l.vars) (e : Together (.fork d l r) s u a b) : Together l s u a b := by
  obtain ⟨f,i,j,hi,hj⟩ := e
  refine ⟨f,i,j,?_⟩
  cases u <;> exact ⟨left_hit dis ha hi,left_hit dis hb hj⟩

private theorem descendR {l r : F} {d u : Bool} {s a b} (dis : l.vars.Disjoint r.vars)
    (ha : a∈r.vars) (hb : b∈r.vars) (e : Together (.fork d l r) s u a b) : Together r s u a b := by
  obtain ⟨f,i,j,hi,hj⟩ := e
  refine ⟨f,i,j,?_⟩
  cases u <;> exact ⟨right_hit dis ha hi,right_hit dis hb hj⟩

theorem incompatible (e : F) (z : Sig) (nd : e.vars.Nodup) (X : Finset Sig) (inside : X⊆e.vars.toFinset)
    (linked : ∀d,Connected (Together e z d) X) {a b : Sig} (ha : a∈X) (hb : b∈X) : a=b := by
  induction e with
  | atom v =>
    have aa : a=v := by simpa [F.vars] using inside ha
    have bb : b=v := by simpa [F.vars] using inside hb
    exact aa.trans bb.symm
  | port => have bad := inside ha; simp [F.vars] at bad
  | fork d l r ih jh =>
    obtain ⟨ll,rr,dis⟩ := List.nodup_append'.mp (show (l.vars++r.vars).Nodup from nd)
    let side := fun x : Sig => decide (x∈l.vars)
    have invariant (x y : Sig) (related : Together (.fork d l r) z d x y) : side x=side y := by
      obtain ⟨f,i,j,hi,hj⟩ := related
      cases d <;> exact (at_side dis _ _ hi).trans (at_side dis _ _ hj).symm
    have same := linked d side (fun x _ y _ xy => invariant x y xy)
    by_cases al : a∈l.vars
    · have sub (w) (hw : w∈X) : w∈l.vars := by
        have eq := same w hw a ha
        simpa [side,al] using eq
      apply ih ll (fun w hw => List.mem_toFinset.mpr (sub w hw))
      intro c f good
      apply linked c f
      intro x hx y hy edge
      exact good x hx y hy (descendL dis (sub x hx) (sub y hy) edge)
    · have sub (w) (hw : w∈X) : w∈r.vars := by
        have eq := same w hw a ha
        have no : w∉l.vars := by simpa [side,al] using eq
        exact (List.mem_append.mp (List.mem_toFinset.mp (inside hw))).resolve_left no
      apply jh rr (fun w hw => List.mem_toFinset.mpr (sub w hw))
      intro c f good
      apply linked c f
      intro x hx y hy edge
      exact good x hx y hy (descendR dis (sub x hx) (sub y hy) edge)

def Edge (X : Finset Sig) (domain : Row→Row→Prop) (d : Bool) (a b : Sig) :=
  ∃ fixed i j : Row, if d then domain fixed i ∧ Forced X fixed i a ∧ domain fixed j ∧ Forced X fixed j b
    else domain i fixed ∧ Forced X i fixed a ∧ domain j fixed ∧ Forced X j fixed b

def Compatible (X : Finset Sig) (domain : Row→Row→Prop) :=
  ∀ Y⊆X, (∀d,Connected (Edge X domain d) Y) → ∀a∈Y,∀b∈Y,a=b

theorem compatible_of (e : F) (z : Sig) (nd : e.vars.Nodup) {X : Finset Sig} (labels : e.vars.toFinset=X)
    (domain : Row→Row→Prop)
    (route : ∀p n,domain p n → ∃ w∈X, e.pick z p n=some w ∧ separates p n w) :
    Compatible X domain := by
  have owns (p n : Row) (a : Sig) (ok : domain p n) (force : Forced X p n a) : e.pick z p n=some a := by
    obtain ⟨w,hw,resp,sep⟩ := route p n ok
    simpa only [force w hw sep] using resp
  have included (d : Bool) {a b} (h : Edge X domain d a b) : Together e z d a b := by
    obtain ⟨fixed,i,j,yes⟩ := h
    refine ⟨fixed,i,j,?_⟩
    cases d <;> simp only [Bool.false_eq_true,↓reduceIte] at yes ⊢ <;>
      exact ⟨owns _ _ _ yes.1 yes.2.1,owns _ _ _ yes.2.2.1 yes.2.2.2⟩
  intro Y sub connected a ha b hb
  apply incompatible e z nd Y (by rwa [labels]) _ ha hb
  intro d f same
  apply connected d f
  intro v hv w hw edge
  exact same v hv w hw (included d edge)

def InGrid (U : Finset Sig) (p n : Row) := (∃m,Miss U p m) ∧ (∃q,Miss U q n)

theorem single_share_necessary {k S} (run : Live k 0 S) (size : S.card=k) :
    ∃ T U : Finset Sig, T.Nonempty ∧ T∪U=S ∧ Disjoint T U ∧
      (∀p n,InGrid U p n → ∃a∈T,separates p n a) ∧
      Compatible T (InGrid U) ∧ Compatible U (Miss T) := by
  obtain ⟨f⟩ := factor run size
  let T := f.inside
  let U := f.outside
  have split := partition f
  obtain ⟨nl,nr,_⟩ := List.nodup_append'.mp f.distinct
  have inner (p n : Row) (ok : InGrid U p n) :=
    inside_answer f (inside_cross f ok.1.choose_spec ok.2.choose_spec)
  refine ⟨T,U,closed_input f.inner f.closed,split.1,split.2,?_,?_,?_⟩
  · intro p n ok
    obtain ⟨a,ha,_,sep⟩ := inner p n ok
    exact ⟨a,ha,sep⟩
  · exact compatible_of f.inner zero nl rfl _ inner
  · exact compatible_of f.outer (f.inner.val zero) nr rfl _ (fun p n no => outside_answer f no)

end CoAO3143.OneShare
