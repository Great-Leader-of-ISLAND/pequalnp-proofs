import PEqualNP.CoProject3456

namespace CoCompile3456
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open CoAO3143Restriction

def one {n} (t : Fin n) : Rows n := fun i => decide (i=t)
def dry (n) (gs : List Gate) : Prop :=
  ∀ j < gs.length, (gs.getD j ⟨.or,[]⟩).op=.and →
    ∀ t : Fin n, (symbolic n gs).getD (n+j) (con false) (one t)=false

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

theorem dry_iff (n) (C : Circuit) : dry n C.gates ↔
    ∀ j < C.gates.length, (gateAt C j).op=.and →
      ∀ t : Fin n, (C.wires (List.ofFn (one t))).getD (n+j) false=false := by
  unfold dry gateAt
  simp only [valRows,Circuit.wires]

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
    funext r
    cases d <;> simp [g,binary,op,readGate,GateOp.eval,ea,eb]
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

private theorem raws {n} (gs : List Gate) (i : Fin n) : var i∈symbolic n gs := by
  have keep {α : Type} (ws : List (Wire α)) (w : Wire α) (hw : w∈ws) (ts : List Gate) :
      w∈circuitWires ts ws := by
    induction ts generalizing ws with
    | nil => exact hw
    | cons g ts ih => exact ih _ (List.mem_append_left _ hw)
  exact keep (raw n) (var i) (List.mem_ofFn.mpr ⟨i,rfl⟩) gs

def accumulated {n} (seed : Wire (Rows n)) (leaves : List (Fin n)) : Wire (Rows n) :=
  leaves.foldl (fun w i => op true w (var i)) seed

theorem accumulated_val {n} (seed : Wire (Rows n)) (leaves : List (Fin n)) (r : Rows n) :
    accumulated seed leaves r = (seed r || leaves.any r) := by
  induction leaves generalizing seed with
  | nil => simp [accumulated]
  | cons j js ih =>
    change accumulated (op true seed (var j)) js r = _
    rw [ih]
    simp [op,var,Bool.or_assoc]

private theorem appendOrs {n} (leaves : List (Fin n)) {gs : List Gate}
    (hg : good n gs) (hd : dry n gs) {a : Wire (Rows n)} (ha : a∈symbolic n gs) :
    ∃ hs : List Gate, hs.length=gs.length+leaves.length ∧ good n hs ∧ dry n hs ∧
      (∀ w∈symbolic n gs,w∈symbolic n hs) ∧ accumulated a leaves ∈symbolic n hs := by
  induction leaves generalizing gs a with
  | nil => exact ⟨gs,by simp,hg,hd,fun _ h => h,ha⟩
  | cons j ls ih =>
    obtain ⟨us,nu,hu,du,preserve,hit⟩ := makeGate hg hd true ha (raws gs j) (by simp)
    obtain ⟨vs,nv,hv,dv,pres2,last⟩ := ih hu du hit
    refine ⟨vs,by simp [nv,nu] <;> omega,hv,dv,fun w hw => pres2 w (preserve w hw),last⟩

theorem appendStar {n} (C : Circuit) (hg : good n C.gates) (hd : dry n C.gates)
    (nonconstant : ¬Constant (circuitFun n C)) (center leaf : Fin n) (ls : List (Fin n))
    (apart : center ∉ leaf::ls) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ dry n D.gates ∧
      D.size=C.size+ls.length+2 ∧ ∀ r : Rows n, circuitFun n D r =
      (circuitFun n C r || (r center && (r leaf || ls.any r))) := by
  let out : Wire (Rows n) := circuitFun n C
  have orig : (symbolic n C.gates).getD C.output (con false)=out := by
    funext r
    exact valRows n C.gates C.output r
  have old : out∈symbolic n C.gates := by
    rw [←orig]
    simp only [List.getD_eq_getElem?_getD]
    cases e : (symbolic n C.gates)[C.output]? with
    | none =>
      have eq : con false=out := by simpa [List.getD_eq_getElem?_getD,e] using orig
      exact (nonconstant ⟨false,eq.symm⟩).elim
    | some a => exact List.mem_of_getElem? e
  obtain ⟨gs,ng,gok,gd,keep,lsum⟩ := appendOrs ls hg hd (raws C.gates leaf)
  have no : ∀ t : Fin n, op false (var center) (accumulated (var leaf) ls) (one t)=false := by
    intro t
    by_cases he : center=t
    · subst t
      have hl : leaf≠center := by intro e; exact apart (List.mem_cons.mpr (Or.inl e.symm))
      have miss : center∉ls := fun h => apart (List.mem_cons_of_mem _ h)
      have off : ls.any (one center)=false := by
        cases h : ls.any (one center) with
        | false => rfl
        | true =>
          obtain ⟨i,hi,ev⟩ := List.any_eq_true.mp h
          have eq : i=center := of_decide_eq_true ev
          exact (miss (eq ▸ hi)).elim
      change ((one center center) && accumulated (var leaf) ls (one center))=false
      rw [accumulated_val,off]
      simp [var,one,hl]
    · simp [op,var,one,he]
  obtain ⟨us,nu,uok,ud,more,prod⟩ := makeGate gok gd false (raws gs center) lsum (fun _ => no)
  obtain ⟨vs,nv,vok,vd,_,finalOut⟩ := makeGate uok ud true (more out (keep out old)) prod (by simp)
  obtain ⟨i,_,ev⟩ := coverIndex finalOut
  refine ⟨⟨vs,i⟩,vok.1,vok.2,vd,?_,?_⟩
  · change vs.length=C.gates.length+ls.length+2
    omega
  · intro r
    change ((⟨vs,i⟩ : Circuit).wires (List.ofFn r)).getD i false=_
    rw [←valRows,ev]
    simp [op,var,out,accumulated_val]

/-- Once the clean normalization conclusion is known for the smaller physical
    residual, an independent star costs exactly the budget recovered by fixing
    its essential vertices to zero. The raw input width is identical throughout. -/
theorem star_recombine {n} (C : Circuit) (cm : Monotone2 C) (R : Finset (Fin n))
    (essential : ∀ i∈R, Essential (circuitFun n C) i)
    (remNonconstant : ¬Constant (cut (freeze R) (circuitFun n C)))
    (center leaf : Fin n) (ls : List (Fin n)) (apart : center∉leaf::ls)
    (count : R.card=ls.length+2)
    (decomp : ∀ r, circuitFun n C r =
      (cut (freeze R) (circuitFun n C) r || (r center && (r leaf || ls.any r))))
    (normalizeResidual : ∀ E : Circuit, Monotone2 E → ReadsBack n E →
      circuitFun n E = cut (freeze R) (circuitFun n C) →
      ∃ P : Circuit, Monotone2 P ∧ ReadsBack n P ∧ dry n P.gates ∧
        P.size ≤ E.size ∧ circuitFun n P = circuitFun n E) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ dry n D.gates ∧
        D.size ≤ C.size ∧ circuitFun n D = circuitFun n C := by
  obtain ⟨E,em,er,cost,ev⟩ := physical_project C cm R essential remNonconstant
  obtain ⟨P,pm,pr,pd,ps,pv⟩ := normalizeResidual E em er ev
  have eq := pv.trans ev
  obtain ⟨D,dm,dr,dd,ds,result⟩ :=
    appendStar P ⟨pm,pr⟩ pd (by rwa [eq]) center leaf ls apart
  refine ⟨D,dm,dr,dd,by omega,?_⟩
  funext r
  rw [result,pv,ev,←decomp]

end CoCompile3456
