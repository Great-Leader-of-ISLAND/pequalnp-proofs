import PEqualNP.CoAO3143Image
import PEqualNP.CoAO3143SevenData
import PEqualNP.CoAO3143CotreeCheck

namespace CoAO3143Restriction.SevenRoots
open CoAO3143

abbrev Extended := Fin 8 → Bool
def input (i : Fin 8) : Wire Extended := fun r => r i
def roots := (List.ofFn input) ++ [con true,con false]

def supplied (x : Fin 7→Bool) (j : Fin 8) : Bool :=
  if h : j.val<7 then x ⟨j.val,h⟩ else !(x 1)
def sample (s : Bool) (i : Row) : Extended := supplied (fun v => bit s i (Seven.vertex v))

def pack (f : Row → Bool) : B := (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn
private theorem pack_bit (f : Row → Bool) (i : Nat) (hi : i<160) :
    (pack f).getLsbD i = f ⟨i,hi⟩ := by
  rw [pack,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
  have h : i < (List.ofFn f).length := by simpa only [List.length_ofFn] using hi
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]
  exact List.getElem_ofFn h

def Q (w : Wire Extended) : Sig :=
  (pack (fun i => w (sample true i)),pack (fun i => w (sample false i)))

theorem Qop (d : Bool) (a b : Wire Extended) : Q (op d a b)=bin d (Q a) (Q b) := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj <;> cases d <;>
    simp only [Q,op,bin,Bool.false_eq_true,↓reduceIte,BitVec.getLsbD_and,BitVec.getLsbD_or,pack_bit _ _ hj]

theorem Qtarget (w : Wire Extended) (f : ∀x, w (supplied x)=Seven.F x) : Q w=target := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (pack _).getLsbD j = (BitVec.allOnes 160).getLsbD j
    rw [pack_bit _ _ hj,BitVec.getLsbD_allOnes]
    simpa [sample,f,Seven.actual_labels,hj]
  · change (pack _).getLsbD j = (0:B).getLsbD j
    rw [pack_bit _ _ hj]
    simp [sample,f,Seven.actual_labels]

set_option maxRecDepth 8192 in
private theorem labels : (roots.map Q).all (fun a => a==zero || a==one || Seven.signed.contains a)=true := by decide +kernel
set_option maxRecDepth 8192 in
private theorem extra : Q (input 7)=Seven.ghost ∧ Seven.ghost∉Seven.raw := by decide +kernel

private theorem back {α : Type} {raw ws : List (Wire α)} {n} (run : Build raw n ws)
    {out : Wire α} {j s} (h : Cone out j s) (sub : ∀x∈s,x∈ws) :
    ∃ k S, k≤n+j ∧ Cone out k S ∧ ∀x∈S,x∈raw := by
  classical
  induction run generalizing j s with
  | start => exact ⟨j,s,by omega,h,sub⟩
  | @gate n ws pre d a b ha hb ih =>
    let z := op d a b
    by_cases use : z∈s
    · let U := s.erase z
      have tail : Cone out j (insert z U) := by simpa [U,Finset.insert_erase use] using h
      have zf : z∉U := by simp [U]
      have keep (w) (hw : w∈U) : w∈ws := by
        obtain ⟨neq,member⟩ := Finset.mem_erase.mp hw
        exact (List.mem_cons.mp (sub w member)).resolve_left neq
      have next := Cone.gate d a b zf tail
      obtain ⟨k,S,le,hS,all⟩ := ih next (by simpa using And.intro ha (And.intro hb keep))
      exact ⟨k,S,by omega,hS,all⟩
    · obtain ⟨k,S,le,hS,all⟩ := ih h (by
        intro w hw
        exact (List.mem_cons.mp (sub w hw)).resolve_left (by intro e; apply use; change op d a b∈s; rw [←e]; exact hw))
      exact ⟨k,S,by omega,hS,all⟩

theorem buildCone {α : Type} {raw ws : List (Wire α)} {n} (run : Build raw n ws)
    {out : Wire α} (hit : out∈ws) :
    ∃ k S, k≤n ∧ Cone out k S ∧ ∀x∈S,x∈raw := by
  obtain ⟨k,S,le,h,sub⟩ := back run (Cone.stop (out:=out)) (by simpa using hit)
  exact ⟨k,S,by omega,h,sub⟩

/-- Failure of both numerical roots excludes a sampled cone that observes its
    negative input on a pair of assignments agreeing on the other seven. -/
theorem exclude (no11 : Impossible 11 0 Seven.signed)
    (no10 : Impossible 10 0 Seven.raw)
    {out : Wire Extended} {k S} (h : Cone out k S) (budget : k≤11) (hs : ∀a∈S,a∈roots)
    (negative : input 7∈S) (solves : ∀ x,out (supplied x)=Seven.F x) : False := by
  classical
  obtain ⟨m,T,le,live,sub,full⟩ := cone_image h Q (Qtarget out solves) Qop
  have subset (w) (hw : w∈T) : w∈Seven.signed := by
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (sub hw)
    have facts := List.all_eq_true.mp labels (Q a) (List.mem_map_of_mem (hs a ha))
    simp only [Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at facts
    rcases facts with (zz|oo)|good
    · exact ((live_proper live _ hw).1 zz).elim
    · exact ((live_proper live _ hw).2 oo).elim
    · exact good
  let xs := Seven.signed.filter (fun a => decide (a∈T))
  have small : xs.Sublist Seven.signed := List.filter_sublist
  have nd : xs.Nodup := Seven.eight_distinct.sublist small
  have same : xs.toFinset=T := by
    ext a
    simp only [xs,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right,fun ha => ⟨subset a ha,ha⟩⟩
  have cover : unionSep false xs=top := by simpa using live_cover live same
  have forms := List.all_eq_true.mp Seven.starts xs (List.mem_sublists.mpr small)
  have choice : xs=Seven.raw ∨ xs=Seven.signed := by simpa [cover] using forms
  rcases choice with ordinary | signed
  · have smaller : m≤10 := by
      by_contra! big
      have eq := full (by omega)
      have g : Q (input 7)∈T := eq ▸ Finset.mem_image_of_mem Q negative
      have g' : Seven.ghost∈xs := List.mem_toFinset.mp (same.symm ▸ (extra.1 ▸ g))
      rw [ordinary] at g'
      exact extra.2 g'
    apply no10 m smaller
    rw [←ordinary,same]
    exact unrestricted live
  · apply no11 m (by omega)
    rw [←signed,same]
    exact unrestricted live

end CoAO3143Restriction.SevenRoots
