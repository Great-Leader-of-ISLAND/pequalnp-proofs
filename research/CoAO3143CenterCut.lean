import PEqualNP.CoAO3143SevenSemantic
import PEqualNP.CoAO3143ThetaPrice

namespace CoAO3143Restriction.CenterCut
open CoAO3143 SevenRoots

abbrev Full := Fin 9→Bool
def raw (i : Fin 9) : Wire Full := fun x => x i
def bank := List.ofFn raw ++ [con true,con false]
def lowerRaw (x : Fin 8→Bool) (j : Fin 9) : Bool :=
  if h : j.val<8 then x ⟨j.val,h⟩ else !(x 2)
def remove (y : Extended) : Full := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7]
def off (x : Small) : Extended := ![x 0,x 1,x 2,x 3,x 4,x 5,x 6,false]
def pin (x : Small) := remove (off x)
def smallLegal (x : Small) : Fin 8→Bool := ![false,x 0,x 1,x 2,x 3,x 4,x 5,x 6]

private theorem agrees : ∀ x : Small, lowerRaw (smallLegal x)=remove (supplied x) ∧
    f8 (smallLegal x)=Seven.F x := by decide +kernel

private theorem full_cs (b : Bool) : con b∈SevenRoots.roots := by
  apply List.mem_append_right
  cases b <;> simp
private theorem plain_cs (b : Bool) : con b∈plain := by
  apply List.mem_append_right
  cases b <;> simp

private theorem remove_known : ∀ a∈bank, cut remove a∈SevenRoots.roots := by
  intro a ha
  rcases List.mem_append.mp ha with hold | cs
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hold
    have facts : ∀ i : Fin 9, cut remove (raw i)=con false ∨
        ∃ j : Fin 8, cut remove (raw i)=SevenRoots.input j := by decide +kernel
    rcases facts i with e | ⟨j,e⟩
    · rw [e]; exact full_cs false
    · rw [e]; exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨_,rfl⟩)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at cs
    rcases cs with rfl | rfl
    · exact full_cs true
    · exact full_cs false

private theorem pin_known : ∀ a∈bank, cut pin a∈plain := by
  intro a ha
  rcases List.mem_append.mp ha with hold | cs
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hold
    have facts : ∀ i : Fin 9, cut pin (raw i)=con false ∨
        ∃ j : Fin 7, cut pin (raw i)=(fun x : Small => x j) := by decide +kernel
    rcases facts i with e | ⟨j,e⟩
    · rw [e]; exact plain_cs false
    · rw [e]; exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨_,rfl⟩)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at cs
    rcases cs with rfl | rfl
    · exact plain_cs true
    · exact plain_cs false

private theorem changedOnly : ∀ i : Fin 8, i≠7 → ∀ x : Small,
    SevenRoots.input i (off x) = SevenRoots.input i (supplied x) := by decide +kernel

private theorem nonconstant : ¬Constant Seven.F := by
  intro h
  obtain ⟨b,eq⟩ := h
  let low : Small := fun _ => false
  let high : Small := fun _ => true
  have one : Seven.F high=true := by decide +kernel
  have zero : Seven.F low=false := by decide +kernel
  rw [eq] at one zero
  exact Bool.false_ne_true (zero.symm.trans one)

private theorem slice_nonconstant {out : Wire Full} (ok : ∀x,out (lowerRaw x)=f8 x) :
    ¬ Constant (cut remove out) := by
  intro h
  obtain ⟨b,eq⟩ := h
  apply nonconstant
  refine ⟨b,?_⟩
  funext x
  have z := congrFun eq (supplied x)
  have w := ok (smallLegal x)
  rw [(agrees x).1,(agrees x).2] at w
  exact w.symm.trans z

/-- The signed center may be chosen as vertex 2. Every true live original
    cone retaining its negative source and peripheral 0 reduces to the
    independent seven-point two-root tests. -/
theorem exclude_center (price : CoThetaNine.SignedLower)
    (n11 : Cotree.cotreeSearch (ProtocolProof.grid 7 10) 11 0 Seven.signed=false)
    (n10 : Cotree.cotreeSearch (ProtocolProof.grid 7 10) 10 0 Seven.raw=false)
    {out : Wire Full} {k S} (live : Cone out k S) (bound : k≤12)
    (rootsAt : ∀ a∈S,a∈bank) (peripheral : raw 0∈S) (negative : raw 8∈S)
    (correct : ∀x,out (lowerRaw x)=f8 x) : False := by
  classical
  have cv : Constant (cut remove (raw 0)) := ⟨false,rfl⟩
  have cv' : Constant (cut pin (raw 0)) := ⟨false,rfl⟩
  have cz' : Constant (cut pin (raw 8)) := ⟨false,rfl⟩
  have different : raw 0≠raw 8 := by decide +kernel
  have active : 1≤losses remove S := by
    have m : raw 0∈S.filter (fun a => Constant (cut remove a)) :=
      Finset.mem_filter.mpr ⟨peripheral,cv⟩
    exact Finset.card_pos.mpr ⟨_,m⟩
  obtain ⟨m,ys,real,outAt,budget⟩ := projected live remove (slice_nonconstant correct)
    (Build.start (raw:=SevenRoots.roots)) full_cs (fun a ha => remove_known a (rootsAt _ ha))
  have cost : m≤11 := by omega
  have equivalent : ∀x, cut remove out (supplied x)=Seven.F x := by
    intro x
    have c := correct (smallLegal x)
    rw [(agrees x).1,(agrees x).2] at c
    exact c
  obtain ⟨j,T,le,tree,rootsAt'⟩ := SevenRoots.buildCone real outAt
  apply SevenRoots.exclude n11 n10 tree (by omega) rootsAt' _ equivalent
  by_contra absent
  have mismatch : cut pin out=Seven.F := by
    funext x
    have same := same_rows tree (off x) (supplied x) (by
      intro w hw
      rcases List.mem_append.mp (rootsAt' w hw) with rawMem | const
      · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp rawMem
        have ni : i≠7 := fun e => absent (e ▸ hw)
        exact changedOnly i ni x
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at const
        rcases const with rfl | rfl <;> rfl)
    exact same.trans (equivalent x)
  have ncon : ¬Constant (cut pin out) := by rw [mismatch]; exact nonconstant
  obtain ⟨l,ss,program,hit,charged⟩ := projected_two live pin ncon plain_cs
    (fun w hw => pin_known w (rootsAt w hw)) different peripheral negative cv' cz'
  rw [mismatch] at hit
  have lb := seven_price price program hit
  omega

end CoAO3143Restriction.CenterCut
