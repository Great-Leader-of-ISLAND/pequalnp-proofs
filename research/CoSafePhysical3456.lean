import PEqualNP.CoStar3456
import PEqualNP.CoSafeFormula3456

namespace CoSafePhysical3456

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open CoAO3143Restriction CoCompile3456 CoSafeFormula3456

/-
The physical address and dry binary append routines below are the previously
kernel-checked CoStar3456 private helpers, reproduced in this namespace so the
formula compiler can supply an arbitrary rooted gate at the physical interface.
-/
private theorem valRows (n gs i) (r : Rows n) :
    (symbolic n gs).getD i (con false) r =
    ((⟨gs,i⟩ : Circuit).wires (List.ofFn r)).getD i false := by
  have ev := circuit_rows gs (raw n) r
  have inps : (raw n).map (fun w => w r) = List.ofFn r := by
    simp only [raw,List.map_ofFn] <;> rfl
  rw [inps] at ev
  change (symbolic n gs).map (fun w => w r) = (⟨gs,i⟩ : Circuit).wires (List.ofFn r) at ev
  rw [←ev]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases (symbolic n gs)[i]? <;> rfl

private theorem coverIndex {n} {gs : List Gate} {a : Wire (Rows n)} (ha : a∈symbolic n gs) :
    ∃ i, i<n+gs.length ∧ (symbolic n gs).getD i (con false)=a := by
  have aux {ws : List (Wire (Rows n))} (h : a∈ws) :
      ∃ i, i<ws.length ∧ ws.getD i (con false)=a := by
    induction ws with
    | nil => simp at h
    | cons w ws ih =>
      rcases List.mem_cons.mp h with rfl|hh
      · exact ⟨0,by simp,by simp⟩
      · obtain ⟨i,hi,hit⟩ := ih hh
        exact ⟨i+1,by simpa using hi,by simpa using hit⟩
  simpa [symLength] using aux ha

private theorem addrRemain {n} {gs} {g : Gate} (i) (h : i<n+gs.length) :
    (symbolic n (gs++[g])).getD i (con false) = (symbolic n gs).getD i (con false) := by
  rw [symSnoc,List.getD_append _ _ _ _ (by simpa [symLength] using h)]

private theorem makeGate {n gs} (hg : good n gs) (hd : dry n gs) (d : Bool)
    {a b : Wire (Rows n)} (ha : a∈symbolic n gs) (hb : b∈symbolic n gs)
    (clean : d=false → ∀ t : Fin n, op d a b (one t)=false) :
    ∃ hs : List Gate, hs.length=gs.length+1 ∧ good n hs ∧ dry n hs ∧
      (∀ w∈symbolic n gs,w∈symbolic n hs) ∧ op d a b∈symbolic n hs := by
  obtain ⟨i,hi,ea⟩ := coverIndex ha
  obtain ⟨j,hj,eb⟩ := coverIndex hb
  let g := binary d i j
  have val : readGate (symbolic n gs) g=op d a b := by
    calc
      _ = op d ((symbolic n gs).getD i (con false)) ((symbolic n gs).getD j (con false)) := by
        funext r
        cases d <;> simp [g,binary,op,readGate,GateOp.eval]
      _ = _ := by rw [ea,eb]
  refine ⟨gs++[g],by simp,goodSnoc hg d i j hi hj,?_,?_,?_⟩
  · intro k hk kind t
    by_cases h : k<gs.length
    · rw [List.getD_append _ _ _ _ h] at kind
      rw [addrRemain (n+k) (by omega)]
      exact hd k h kind t
    · simp only [List.length_append,List.length_cons,List.length_nil] at hk
      have he : k=gs.length := by omega
      subst k
      have lg : (gs++[g]).getD gs.length ⟨.or,[]⟩ = g := by simp
      rw [lg] at kind
      have hd' : d=false := by cases d <;> simp_all [g,binary]
      rw [symSnoc,←symLength n gs]
      have last : (symbolic n gs++[readGate (symbolic n gs) g]).getD
          (symbolic n gs).length (con false)=readGate (symbolic n gs) g := by simp
      rw [last,val]
      exact clean hd' t
  · intro w hw
    rw [symSnoc]
    exact List.mem_append_left _ hw
  · rw [symSnoc]
    exact List.mem_append_right _ (by simp [val])

variable {ι : Type*}

def value {n} (bank : ι → Wire (Rows n)) : Tree ι → Wire (Rows n)
  | .leaf i => bank i
  | .both a b => op false (value bank a) (value bank b)
  | .either a b => op true (value bank a) (value bank b)

theorem value_iff {n} (bank : ι → Wire (Rows n)) (t : Tree ι) (r : Rows n) :
    value bank t r = true ↔ holds (fun i => bank i r = true) t := by
  induction t with
  | leaf i => rfl
  | both a b ia ib => simp [value,op,holds,ia,ib]
  | either a b ia ib => simp [value,op,holds,ia,ib]

theorem append_formula {n} (bank : ι → Wire (Rows n)) (t : Tree ι) {gs : List Gate}
    (hg : good n gs) (hd : dry n gs) (hp : ∀ i, bank i ∈ symbolic n gs)
    (dryTree : ∀ v : Fin n, clean (fun i => bank i (one v) = true) t) :
    ∃ hs : List Gate, hs.length = gs.length + gates t ∧ good n hs ∧ dry n hs ∧
      (∀ w ∈ symbolic n gs, w ∈ symbolic n hs) ∧ value bank t ∈ symbolic n hs := by
  induction t generalizing gs with
  | leaf i => exact ⟨gs,by simp [gates],hg,hd,fun _ hw => hw,hp i⟩
  | both a b ia ib =>
    obtain ⟨ags,ca,ga,da,ka,va⟩ := ia hg hd hp (fun v => (dryTree v).1)
    obtain ⟨bgs,cb,gb,db,kb,vb⟩ := ib ga da (fun i => ka _ (hp i)) (fun v => (dryTree v).2.1)
    have ok : ∀ v : Fin n, op false (value bank a) (value bank b) (one v) = false := by
      intro v
      cases hh : op false (value bank a) (value bank b) (one v) with
      | false => rfl
      | true =>
        have hit := (value_iff bank (.both a b) (one v)).1 hh
        exact ((dryTree v).2.2 hit).elim
    obtain ⟨hs,nc,gc,dc,kc,vc⟩ := makeGate gb db false (kb _ va) vb (fun _ => ok)
    refine ⟨hs,?_,gc,dc,fun w hw => kc w (kb w (ka w hw)),vc⟩
    simp only [gates]
    omega
  | either a b ia ib =>
    obtain ⟨ags,ca,ga,da,ka,va⟩ := ia hg hd hp (fun v => (dryTree v).1)
    obtain ⟨bgs,cb,gb,db,kb,vb⟩ := ib ga da (fun i => ka _ (hp i)) (fun v => (dryTree v).2)
    obtain ⟨hs,nc,gc,dc,kc,vc⟩ := makeGate gb db true (kb _ va) vb (by simp)
    refine ⟨hs,?_,gc,dc,fun w hw => kc w (kb w (ka w hw)),vc⟩
    simp only [gates]
    omega

theorem physical_formula {n} (bank : ι → Wire (Rows n)) (t : Tree ι) {gs : List Gate}
    (hg : good n gs) (hd : dry n gs) (hp : ∀ i, bank i ∈ symbolic n gs)
    (dryTree : ∀ v : Fin n, clean (fun i => bank i (one v) = true) t) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ dry n D.gates ∧
      D.size = gs.length + gates t ∧ circuitFun n D = value bank t := by
  obtain ⟨hs,hsize,hg',hd',_,out⟩ := append_formula bank t hg hd hp dryTree
  obtain ⟨i,_,hi⟩ := coverIndex out
  refine ⟨⟨hs,i⟩,hg'.1,hg'.2,hd',hsize,?_⟩
  funext r
  have h := valRows n hs i r
  rw [hi] at h
  exact h.symm

end CoSafePhysical3456
