import PEqualNP.CoIsolatedStar3456

/- Adapted from our kernel-checked CoStar3456.appendStar. Here an arbitrary old
prefix is retained verbatim, including temporarily invalid pins; new gates read only
valid earlier slots. The dry predicate explicitly covers the empty row as requested. -/
namespace Co5282Attach
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CoCompile3456 CoAO3143Restriction

def purePrefix (n : Nat) (gs : List Gate) := Monotone2 ⟨gs,0⟩
def bitrow {n} (S : Finset (Fin n)) (v : Fin n) := decide (v ∈ S)
def cleanS (n : Nat) (gs : List Gate) : Prop :=
  ∀ j < gs.length, (gs.getD j ⟨.or,[]⟩).op=.and →
  ∀ S : Finset (Fin n), S.card ≤ 1 → (symbolic n gs).getD (n+j) (con false) (bitrow S)=false

private theorem newGate {n gs} (baseOK : purePrefix n gs) (d : Bool) (i j : Nat) :
    purePrefix n (gs++[binary d i j]) := by
  intro gate hg
  rcases List.mem_append.mp hg with prev | last
  · exact baseOK gate prev
  · have eq : gate = binary d i j := List.mem_singleton.mp last
    subst gate
    cases d <;> simp [binary]

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

private theorem makeGate {n gs} (hg : purePrefix n gs) (hd : cleanS n gs) (d : Bool)
    {a b : Wire (Rows n)} (ha : a∈symbolic n gs) (hb : b∈symbolic n gs)
    (clean : d=false → ∀ S : Finset (Fin n), S.card ≤ 1 → op d a b (bitrow S)=false) :
    ∃ hs : List Gate, hs.length=gs.length+1 ∧ purePrefix n hs ∧ cleanS n hs ∧
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
  refine ⟨gs++[g],by simp,newGate (n := n) hg d i j,?_,?_,?_⟩
  · intro k hk kind S small
    by_cases h : k<gs.length
    · rw [List.getD_append _ _ _ _ h] at kind
      rw [addrRemain (n+k) (by omega)]
      exact hd k h kind S small
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
      exact clean hd' S small
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


private theorem appendOrs {n} (leaves : List (Fin n)) {gs : List Gate}
    (hg : purePrefix n gs) (hd : cleanS n gs) {a : Wire (Rows n)} (ha : a∈symbolic n gs) :
    ∃ hs : List Gate, hs.length=gs.length+leaves.length ∧ purePrefix n hs ∧ cleanS n hs ∧
      (∀ w∈symbolic n gs,w∈symbolic n hs) ∧ accumulated a leaves ∈symbolic n hs := by
  induction leaves generalizing gs a with
  | nil => exact ⟨gs,by simp,hg,hd,fun _ h => h,ha⟩
  | cons j ls ih =>
    obtain ⟨us,nu,hu,du,preserve,hit⟩ := makeGate hg hd true ha (raws gs j) (by simp)
    obtain ⟨vs,nv,hv,dv,pres2,last⟩ := ih hu du hit
    refine ⟨vs,by simp [nv,nu] <;> omega,hv,dv,fun w hw => pres2 w (preserve w hw),last⟩

theorem appendStar {n} (C : Circuit) (hg : purePrefix n C.gates) (hd : cleanS n C.gates)
    (positive : ∃ r : Rows n, circuitFun n C r = true) (center leaf : Fin n) (ls : List (Fin n))
    (apart : center ∉ leaf::ls) :
    ∃ D : Circuit, Monotone2 D ∧ cleanS n D.gates ∧
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
      obtain ⟨r,on⟩ := positive
      have bad := congrFun eq r
      change false = circuitFun n C r at bad
      rw [on] at bad
      contradiction
    | some a => exact List.mem_of_getElem? e
  obtain ⟨gs,ng,gok,gd,keep,lsum⟩ := appendOrs ls hg hd (raws C.gates leaf)
  have no : ∀ S : Finset (Fin n), S.card ≤ 1 →
      op false (var center) (accumulated (var leaf) ls) (bitrow S) = false := by
    intro S small
    by_cases hc : center ∈ S
    · have leafOff : leaf ∉ S := by
        intro h
        have e := Finset.card_le_one.mp small leaf h center hc
        exact apart (List.mem_cons.mpr (Or.inl e.symm))
      have restOff : ls.any (bitrow S) = false := by
        cases ht : ls.any (bitrow S) with
        | false => rfl
        | true =>
          obtain ⟨j,hj,on⟩ := List.any_eq_true.mp ht
          have eq := Finset.card_le_one.mp small j (of_decide_eq_true on) center hc
          exact (apart (List.mem_cons_of_mem _ (eq ▸ hj))).elim
      change (bitrow S center && accumulated (var leaf) ls (bitrow S)) = false
      rw [accumulated_val,restOff]
      simp [bitrow,var,leafOff]
    · simp [op,var,bitrow,hc]
  obtain ⟨us,nu,uok,ud,more,prod⟩ := makeGate gok gd false (raws gs center) lsum (fun _ => no)
  obtain ⟨vs,nv,vok,vd,_,finalOut⟩ := makeGate uok ud true (more out (keep out old)) prod (by simp)
  obtain ⟨i,_,ev⟩ := coverIndex finalOut
  refine ⟨⟨vs,i⟩,vok,vd,?_,?_⟩
  · change vs.length=C.gates.length+ls.length+2
    omega
  · intro r
    change ((⟨vs,i⟩ : Circuit).wires (List.ofFn r)).getD i false=_
    rw [←valRows,ev]
    simp [op,var,out,accumulated_val]


theorem attach : ∀ (n : ℕ) (c : Fin n) (L : Finset (Fin n)),
    let Dry := fun (C : Circuit) => ∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
      ∀ S : Finset (Fin n), S.card ≤ 1 →
      (C.wires (List.ofFn fun i => decide (i ∈ S))).getD (n+j) false = false
    L.Nonempty → c ∉ L → ∀ C : Circuit, Monotone2 C → Dry C →
    (∃ r : Fin n → Bool, C.eval (List.ofFn r) = true) →
    ∃ D : Circuit, Monotone2 D ∧ Dry D ∧ D.size ≤ C.size + L.card + 1 ∧
      ∀ r : Fin n → Bool, D.eval (List.ofFn r) = true ↔
       C.eval (List.ofFn r) = true ∨ (r c = true ∧ ∃ j ∈ L, r j = true) := by
  intro n c L
  dsimp only
  intro nonempty apart C cm old pos
  have olddry : cleanS n C.gates := by
    intro j hj hop S small
    have got : C.gates[j]? = some (C.gates.getD j ⟨.or,[]⟩) := by
      simp [List.getD_eq_getElem?_getD,hj]
    rw [valRows]
    exact old j _ got hop S small
  cases listEq : L.toList with
  | nil =>
    obtain ⟨j,hj⟩ := nonempty
    have mem : j ∈ L.toList := by simpa using hj
    simp [listEq] at mem
  | cons leaf ls =>
    have mem (j : Fin n) : j∈leaf::ls ↔ j∈L := by rw [←listEq]; simp
    have len : ls.length + 1 = L.card := by
      have e := congrArg List.length listEq
      simpa using e.symm
    obtain ⟨D,dm,dd,sz,run⟩ := Co5282Attach.appendStar C cm olddry pos c leaf ls
      (fun h => apart ((mem c).mp h))
    refine ⟨D,dm,?_,by omega,?_⟩
    · intro j g hg hand S small
      have hj : j < D.gates.length := by
        by_contra! high
        have none : D.gates[j]? = none := List.getElem?_eq_none (by omega)
        rw [none] at hg
        cases hg
      have gate : D.gates.getD j ⟨.or,[]⟩ = g := by simp [List.getD_eq_getElem?_getD,hg]
      have kind : (D.gates.getD j ⟨.or,[]⟩).op = .and := by rw [gate]; exact hand
      have off := dd j hj kind S small
      rw [valRows] at off
      exact off
    · intro r
      change circuitFun n D r = true ↔ _
      rw [run r,Bool.or_eq_true,Bool.and_eq_true]
      have hit : (r leaf || ls.any r) = true ↔ ∃ j∈L, r j = true := by
        change (leaf::ls).any r = true ↔ _
        rw [List.any_eq_true]
        exact exists_congr (fun j => and_congr (mem j) Iff.rfl)
      rw [hit]
      exact Iff.rfl

#print axioms attach
end Co5282Attach
