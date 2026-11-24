import PEqualNP.CoAO3143CenterCut

namespace CoAO3143Restriction.Physical
open CoAO3143

abbrev V8 := Fin 8 → Bool
def pure (i : Fin 8) : Wire V8 := fun x => x i
def positiveRoots := List.ofFn pure ++ [con true,con false]
def OrdinaryPrice : Prop := ∀ {n ws}, Build positiveRoots n ws → f8∈ws → 13≤n

private theorem preserves {α : Type} (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (ws : List (Wire α)) : ∀w∈ws,w∈circuitWires gs ws := by
  induction gs generalizing ws with
  | nil => exact fun _ h => h
  | cons g gs ih =>
    intro w hw
    exact ih (ws++[readGate ws g]) w (List.mem_append_left _ hw)

private theorem default_member {α : Type} (xs : List (Wire α)) (i : Nat) (d : Wire α) (hd : d∈xs) :
    xs.getD i d∈xs := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : xs[i]? with
  | none => exact hd
  | some w => exact List.mem_of_getElem? e

theorem cone_mono {α : Type} {out : Wire α} {k S} (h : Cone out k S) (r s : α)
    (order : ∀ w∈S,w r=true → w s=true) (yes : out r=true) : out s=true := by
  induction h with
  | stop => exact order _ (by simp) yes
  | @gate k U d a b fresh tail ih =>
    apply ih _ yes
    intro w hw hit
    rcases Finset.mem_insert.mp hw with rfl | old
    · have ha := order a (Finset.mem_insert_self _ _)
      have hb := order b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      cases d <;> simp only [op,Bool.false_eq_true,↓reduceIte,Bool.and_eq_true,Bool.or_eq_true] at hit ⊢
      · exact ⟨ha hit.1,hb hit.2⟩
      · exact hit.imp ha hb
    · exact order w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem old)) hit

def inject (pivot : Fin 8) (x : V8) (j : Fin 9) : Bool :=
  if h : j.val<8 then x ⟨j.val,h⟩ else !(x pivot)
def literals (x : V8) (j : Fin 9) : Bool :=
  if h : j.val<8 then x ⟨j.val,h⟩ else false

private theorem true_false : ¬Constant f8 := by
  rintro ⟨b,h⟩
  have hi : f8 (fun _ => true)=true := by decide +kernel
  have lo : f8 (fun _ => false)=false := by decide +kernel
  rw [h] at hi lo
  exact Bool.false_ne_true (lo.symm.trans hi)

private theorem needs_negative {out : Wire CenterCut.Full} {k S} (live : Cone out k S)
    (small : k≤12) (raws : ∀a∈S,a∈CenterCut.bank) (p : Fin 8)
    (agrees : ∀x,out (inject p x)=f8 x) (ordinary : OrdinaryPrice) : CenterCut.raw 8∈S := by
  classical
  by_contra missing
  have same : cut literals out=f8 := by
    funext x
    have e := same_rows live (literals x) (inject p x) (by
      intro w hw
      rcases List.mem_append.mp (raws w hw) with var | fixed
      · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp var
        have ne : i≠8 := by intro eq; subst i; exact missing hw
        have lt : i.val<8 := by omega
        simp [CenterCut.raw,literals,inject,lt]
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at fixed
        rcases fixed with rfl|rfl <;> rfl)
    exact e.trans (agrees x)
  have nc : ¬Constant (cut literals out) := by rw [same]; exact true_false
  have constants (b : Bool) : con b∈positiveRoots := by
    apply List.mem_append_right
    cases b <;> simp
  have known (w) (hw : w∈S) : cut literals w∈positiveRoots := by
    rcases List.mem_append.mp (raws w hw) with var | fixed
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp var
      by_cases lt : i.val<8
      · have eq : cut literals (CenterCut.raw i) = pure ⟨i.val,lt⟩ := by funext x; simp [cut,CenterCut.raw,literals,pure,lt]
        rw [eq]; exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨_,rfl⟩)
      · have eq : cut literals (CenterCut.raw i) = con false := by funext x; simp [cut,con,CenterCut.raw,literals,lt]
        rw [eq]; exact constants false
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at fixed
      rcases fixed with rfl|rfl
      · exact constants true
      · exact constants false
  obtain ⟨m,zs,build,hit,cap⟩ := projected live literals nc (Build.start (raw:=positiveRoots)) constants known
  rw [same] at hit
  have bnd := ordinary (by simpa using build) hit
  omega

private theorem needs_peripheral {out : Wire CenterCut.Full} {k S} (live : Cone out k S)
    (raws : ∀a∈S,a∈CenterCut.bank) (p : Fin 8)
    (agrees : ∀x,out (inject p x)=f8 x) : CenterCut.raw 0∈S := by
  classical
  let high : V8 := ![true,true,false,false,false,false,false,false]
  let low : V8 := ![false,true,false,false,false,false,false,false]
  have positive : f8 high=true := by decide +kernel
  have negative : f8 low=false := by decide +kernel
  by_contra missing
  have z : ∀ (i : Fin 9) (j : Fin 8), i≠0 →
      CenterCut.raw i (inject j high)=true → CenterCut.raw i (inject j low)=true := by decide +kernel
  have outLow := cone_mono live (inject p high) (inject p low) (by
    intro w hw hit
    rcases List.mem_append.mp (raws w hw) with var | fixed
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp var
      exact z i p (fun eq => missing (eq ▸ hw)) hit
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at fixed
      rcases fixed with rfl|rfl <;> exact hit)
    ((agrees high).trans positive)
  rw [agrees,negative] at outLow
  exact Bool.false_ne_true outLow

private theorem outer_cut (price : CoThetaNine.SignedLower) {out : Wire CenterCut.Full} {k S}
    (live : Cone out k S) (cap : k≤12) (raws : ∀a∈S,a∈CenterCut.bank)
    (p0 : CenterCut.raw 0∈S) (z : CenterCut.raw 8∈S) (agrees : ∀x,out (inject 0 x)=f8 x) : False := by
  let lift : Small→CenterCut.Full := fun x => inject 0 (CenterCut.smallLegal x)
  have outEq : cut lift out=Seven.F := by
    funext x
    have ev := agrees (CenterCut.smallLegal x)
    have test : ∀ x : Small,f8 (CenterCut.smallLegal x)=Seven.F x := by decide +kernel
    exact ev.trans (test x)
  have c0 : Constant (cut lift (CenterCut.raw 0)) := ⟨false,rfl⟩
  have c8 : Constant (cut lift (CenterCut.raw 8)) := ⟨true,rfl⟩
  have nc : ¬Constant (cut lift out) := by
    rw [outEq]
    rintro ⟨b,e⟩
    have hi : Seven.F (fun _ => true)=true := by decide +kernel
    have lo : Seven.F (fun _ => false)=false := by decide +kernel
    rw [e] at hi lo
    exact Bool.false_ne_true (lo.symm.trans hi)
  have cs (b : Bool) : con b∈plain := by
    apply List.mem_append_right
    cases b <;> simp
  have known (w) (hw : w∈S) : cut lift w∈plain := by
    rcases List.mem_append.mp (raws w hw) with var | fixed
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp var
      have proof : ∀ i : Fin 9, (∃ b,cut lift (CenterCut.raw i)=con b) ∨
        ∃ j : Fin 7,cut lift (CenterCut.raw i)=(fun x : Small => x j) := by decide +kernel
      rcases proof i with ⟨b,eq⟩ | ⟨j,eq⟩
      · rw [eq]; exact cs b
      · rw [eq]; exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨_,rfl⟩)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at fixed
      rcases fixed with rfl|rfl
      · exact cs true
      · exact cs false
  obtain ⟨m,ys,build,hit,budget⟩ := projected_two live lift nc cs known
    (show CenterCut.raw 0≠CenterCut.raw 8 by decide +kernel) p0 z c0 c8
  rw [outEq] at hit
  have lb := seven_price price build hit
  omega

def rotation (p : Fin 8) : Fin 8→Fin 8 := ![![0,1,2,3,4,5,6,7],![3,2,1,0,7,6,5,4],![0,1,2,3,4,5,6,7],![3,2,1,0,7,6,5,4],![3,7,4,0,2,5,6,1],![5,1,2,6,7,0,3,4],![5,7,4,6,1,3,0,2],![0,4,7,3,1,6,5,2]] p
def pivot (j : Fin 8) : Fin 8 := if outer j then 0 else 2
def initial (j : Fin 8) : List (Wire CenterCut.Full) :=
  List.ofFn (fun i => CenterCut.raw (rotation j i).castSucc) ++ [CenterCut.raw 8,con true,con false]

private theorem initial_subset (j : Fin 8) : ∀ a∈initial j,a∈CenterCut.bank := by
  intro a ha
  rcases List.mem_append.mp ha with var|extra
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp var
    exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨_,rfl⟩)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at extra
    rcases extra with rfl|rfl|rfl
    · exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨8,rfl⟩)
    · exact List.mem_append_right _ (by simp)
    · exact List.mem_append_right _ (by simp)

set_option maxRecDepth 8192 in
private theorem transport : ∀ (j : Fin 8) (x : V8),
    (initial j).map (fun w => w (inject (pivot j) x)) =
      List.ofFn (fun i => x (rotation j i)) ++ [!(x (rotation j j)),true,false] ∧
    f8 (fun i => x (rotation j i))=f8 x := by decide +kernel

/-- Physical arbitrary-pin no-NOT branch of the official eight-variable
    theorem. Its only finite obstructions are two concrete seven-point roots. -/
theorem ao_lower (price : CoThetaNine.SignedLower) (ordinary : OrdinaryPrice)
    (n11 : Impossible 11 0 Seven.signed)
    (n10 : Impossible 10 0 Seven.raw)
    (j : Fin 8) (C : PEqualNP.CircuitLowerBounds.Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C)
    (no : ∀ g∈C.gates,g.op≠.not)
    (agree : ∀x : V8,C.eval (List.ofFn x++[!(x j),true,false])=f8 x) : 13≤C.size := by
  classical
  by_contra! small
  let U := circuitWires C.gates (initial j)
  let out := U.getD C.output (con false)
  have cs (b : Bool) : con b∈initial j := by
    apply List.mem_append_right
    cases b <;> simp
  have hit : out∈U := default_member _ _ _ (preserves C.gates (initial j) _ (cs false))
  have legal (g) (hg : g∈C.gates) : (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by
    obtain ⟨h,hlen⟩ := fan g hg
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
    exact ⟨h.elim Or.inl (fun h => Or.inr (h.resolve_right (no g hg))),hlen⟩
  obtain ⟨k,S,length,cone,rawSubset⟩ := physical_cone out C.gates (initial j) cs legal hit
  have bound : k≤12 := by change C.gates.length < 13 at small; omega
  have sub (a) (ha : a∈S) : a∈CenterCut.bank := initial_subset j a (rawSubset a ha)
  have valid (x : V8) : out (inject (pivot j) x)=f8 x := by
    let r := inject (pivot j) x
    have ev := congrArg (fun w : List Bool => w.getD C.output false) (circuit_rows C.gates (initial j) r)
    have read : (U.map (fun f => f r)).getD C.output false = out r := by
      simp only [out,List.getD_eq_getElem?_getD,List.getElem?_map]
      cases U[C.output]? <;> rfl
    change (U.map (fun f => f r)).getD C.output false = _ at ev
    rw [read] at ev
    have initialEq := (transport j x).1
    change (initial j).map (fun w => w r) = _ at initialEq
    rw [initialEq] at ev
    exact ev.trans ((agree (fun i => x (rotation j i))).trans (transport j x).2)
  have neg := needs_negative cone bound sub (pivot j) valid ordinary
  have periph := needs_peripheral cone sub (pivot j) valid
  by_cases e : outer j
  · have eq : pivot j=0 := by simp [pivot,e]
    exact outer_cut price cone bound sub periph neg (by simpa only [eq] using valid)
  · have eq : pivot j=2 := by simp [pivot,e]
    exact CenterCut.exclude_center price n11 n10 cone bound sub periph neg (by simpa only [eq,CenterCut.lowerRaw,inject] using valid)

end CoAO3143Restriction.Physical
