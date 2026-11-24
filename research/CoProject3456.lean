import PEqualNP.CoCompile3456
namespace CoCompile3456
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open CoAO3143Restriction

def var {n : Nat} (i : Fin n) : Wire (Rows n) := fun r => r i
def freeze {n : Nat} (R : Finset (Fin n)) (r : Rows n) : Rows n :=
  fun i => if i ∈ R then false else r i
def Essential {n} (out : Wire (Rows n)) (i : Fin n) : Prop :=
  ∃ r s : Rows n, (∀ j, j ≠ i → r j=s j) ∧ out r ≠ out s

private theorem fetch {α : Type} (ws : List (Wire α)) (i : Nat) :
    ws.getD i (con false)∈ws ∨ Constant (ws.getD i (con false)) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : ws[i]? with
  | none => exact Or.inr ⟨false,rfl⟩
  | some a => exact Or.inl (List.mem_of_getElem? h)

private theorem classify {α : Type} (ws : List (Wire α)) (g : Gate)
    (legal : (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) :
    Constant (readGate ws g) ∨ ∃ d a b, (a ∈ ws ∨ Constant a) ∧ (b ∈ ws ∨ Constant b) ∧
      readGate ws g=op d a b := by
  rcases g with ⟨kind,ins⟩
  obtain ⟨hk,hlen⟩ := legal
  change kind=.and ∨ kind=.or at hk
  change ins.length≤2 at hlen
  cases ins with
  | nil =>
    left
    rcases hk with rfl|rfl
    · exact ⟨true,rfl⟩
    · exact ⟨false,rfl⟩
  | cons i is =>
    cases is with
    | nil =>
      right
      rcases hk with rfl|rfl
      · exact ⟨false,_,_,fetch ws i,fetch ws i,by funext x; simp [readGate,GateOp.eval,op]⟩
      · exact ⟨true,_,_,fetch ws i,fetch ws i,by funext x; simp [readGate,GateOp.eval,op]⟩
    | cons j js =>
      cases js with
      | nil =>
        right
        rcases hk with rfl|rfl
        · exact ⟨false,_,_,fetch ws i,fetch ws j,by funext x; simp [readGate,GateOp.eval,op]⟩
        · exact ⟨true,_,_,fetch ws i,fetch ws j,by funext x; simp [readGate,GateOp.eval,op]⟩
      | cons k ks => simp at hlen

/-- The two free constants live in the proof pool, never among the physical raw
    inputs; this preserves all physical gate addresses without a shift. -/
theorem looseCone {α : Type} (out : Wire α) (gs : List Gate) (ws : List (Wire α))
    (legal : ∀ g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (hit : out∈circuitWires gs ws ∨ Constant out) :
    ∃ k S, k≤gs.length ∧ Cone out k S ∧ ∀ a∈S, a∈ws ∨ Constant a := by
  classical
  induction gs generalizing ws with
  | nil => exact ⟨0,{out},by simp,Cone.stop,by simpa [circuitWires] using hit⟩
  | cons g gs ih =>
    let z := readGate ws g
    obtain ⟨k,S,bound,tail,src⟩ := ih (ws++[z]) (fun a ha => legal a (List.mem_cons_of_mem _ ha)) hit
    by_cases use : z ∈ S
    · by_cases fixed : z ∈ ws ∨ Constant z
      · refine ⟨k,S,by simp; omega,tail,?_⟩
        intro w hw
        rcases src w hw with hh | hc
        · rcases List.mem_append.mp hh with old|last
          · exact Or.inl old
          · rw [List.mem_singleton.mp last]
            exact fixed
        · exact Or.inr hc
      · rcases classify ws g (legal g List.mem_cons_self) with constant | ⟨d,a,b,ha,hb,e⟩
        · exact (fixed (Or.inr constant)).elim
        let U := S.erase z
        have eq : z=op d a b := e
        have fresh : op d a b∉U := by simp [U,←eq]
        have next : Cone out k (insert (op d a b) U) := by simpa [U,←eq,Finset.insert_erase use] using tail
        refine ⟨k+1,_,by simpa using bound,Cone.gate d a b fresh next,?_⟩
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact ha
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact hb
        obtain ⟨ne,hs⟩ := Finset.mem_erase.mp hw
        rcases src w hs with hh | hc
        · rcases List.mem_append.mp hh with old|last
          · exact Or.inl old
          · exact (ne (List.mem_singleton.mp last)).elim
        · exact Or.inr hc
    · refine ⟨k,S,by simp; omega,tail,?_⟩
      intro w hw
      rcases src w hw with hh | hc
      · rcases List.mem_append.mp hh with old|last
        · exact Or.inl old
        · exact (use ((List.mem_singleton.mp last) ▸ hw)).elim
      · exact Or.inr hc

private theorem varInj {n : Nat} : Function.Injective (@var n) := by
  intro i j eq
  by_contra ne
  have hh := congrFun eq (fun t => decide (t=i))
  simp [var,Ne.symm ne] at hh

theorem keepEssential {n k S} {out : Wire (Rows n)} (live : Cone out k S)
    (sources : ∀ w∈S, w∈raw n ∨ Constant w) {i : Fin n} (hi : Essential out i) :
    var i∈S := by
  obtain ⟨r,s,same,changes⟩ := hi
  by_contra absent
  apply changes
  apply same_rows live r s
  intro w hw
  rcases sources w hw with hv|⟨b,rfl⟩
  · obtain ⟨j,eq⟩ := List.mem_ofFn.mp hv
    have e : var j=w := eq
    rw [←e]
    apply same j
    rintro rfl
    exact absent (e.symm ▸ hw)
  · rfl

theorem physical_project {n : Nat} (C : Circuit) (hc : Monotone2 C) (R : Finset (Fin n))
    (essential : ∀ i ∈ R, Essential (circuitFun n C) i)
    (nc : ¬Constant (cut (freeze R) (circuitFun n C))) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size+R.card ≤ C.size ∧
      circuitFun n D = cut (freeze R) (circuitFun n C) := by
  classical
  let ws := symbolic n C.gates
  let F := ws.getD C.output (con false)
  have eq : F=circuitFun n C := by
    funext r
    have er := circuit_rows C.gates (raw n) r
    have inp : (raw n).map (fun w => w r) = List.ofFn r := by
      simp only [raw,List.map_ofFn] <;> rfl
    rw [inp] at er
    change ws.map (fun w => w r) = C.wires (List.ofFn r) at er
    change ws.getD C.output (con false) r=(C.wires (List.ofFn r)).getD C.output false
    rw [←er]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ws[C.output]? <;> rfl
  have hit : F∈ws ∨ Constant F := fetch ws C.output
  have legal g (hg : g∈C.gates) : (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by
    obtain ⟨ops,len⟩ := hc g hg
    exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ops,len⟩
  obtain ⟨k,S,lim,live,source⟩ := looseCone F C.gates (raw n) legal hit
  have cs (b : Bool) : con b ∈ free n := by cases b <;> simp [free]
  have entry w (hw : w∈S) : cut (freeze R) w∈free n := by
    rcases source w hw with hv | ⟨b,rfl⟩
    · obtain ⟨j,eqj⟩ := List.mem_ofFn.mp hv
      have e : var j=w := eqj
      rw [←e]
      by_cases hj : j∈R
      · have h0 : cut (freeze R) (var j) = con false := by funext r; simp [cut,freeze,var,con,hj]
        rw [h0]; exact cs false
      · have he : cut (freeze R) (var j) = var j := by funext r; simp [cut,freeze,var,hj]
        rw [he]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨j,rfl⟩))
    · exact cs b
  obtain ⟨m,ys,build,sol,pay⟩ := projected live (freeze R) (by rwa [eq]) (Build.start (raw:=free n)) cs entry
  have sub : R.image var ⊆ S.filter (fun w => Constant (cut (freeze R) w)) := by
    intro w hw
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
    have hj' := keepEssential live source (show Essential F j by rw [eq]; exact essential j hj)
    exact Finset.mem_filter.mpr ⟨hj',false,by funext r; simp [cut,freeze,var,con,hj]⟩
  have box := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ varInj] at box
  change R.card ≤ losses (freeze R) S at box
  obtain ⟨D,dm,dr,ds,de⟩ := compile (show Build (free n) m ys by simpa using build) sol (by rwa [eq])
  refine ⟨D,dm,dr,?_,?_⟩
  · change D.size+R.card ≤ C.gates.length
    omega
  · simpa [eq] using de

end CoCompile3456
