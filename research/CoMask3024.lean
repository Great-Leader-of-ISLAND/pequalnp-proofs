import PEqualNP.CoAO3143ThetaPrice
namespace CoMask3024
open CoThetaNine CoThetaFreeCore CoAO3143Restriction
noncomputable section
local instance {α : Type} : DecidableEq (Wire α) := Classical.decEq _

def marked (c : Fin 4) : Fin 9 := ![0,2,4,7] c
def mate (c : Fin 4) : Fin 9 := ![4,7,0,2] c
def slice (c : Fin 4) := sliceLift (![0,2,0,2] c)
def neg (c : Fin 4) : Wire Input := fun r => !(vtx (marked c) r)
def lab (c : Fin 4) (i : Fin 13) : Wire Input :=
  if hi : i.val<9 then vtx ⟨i.val,hi⟩ else if i.val=9 then fun r => vtx 0 r || vtx 2 r
  else if i.val=10 then neg c else con (decide (i.val=12))
def axis (c : Fin 4) (which : Bool) := if which then marked c else mate c
def lo (i : Fin 9) : Input := row (![20,0,9,0,1,0,0,4,0] i)
def hi (i : Fin 9) : Input := row ((lo i).val ||| (1 <<< i.val))
def bank7 : List (Wire SmallInput) := List.ofFn raw7++[con false,con true]

theorem ordered {α : Type} {out : Wire α} {k S} (h : Cone out k S) (r s : α)
    (step : ∀ w∈S, w r=true → w s=true) (yes : out r=true) : out s=true := by
  induction h with
  | stop => exact step _ (by simp) yes
  | @gate k U d a b fresh tail ih =>
    apply ih
    intro w hw hit
    rcases Finset.mem_insert.mp hw with rfl|old
    · have ha := step a (Finset.mem_insert_self _ _)
      have hb := step b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      cases d <;> simp only [op,Bool.false_eq_true,↓reduceIte,Bool.and_eq_true,Bool.or_eq_true] at hit ⊢
      · exact ⟨ha hit.1,hb hit.2⟩
      · exact hit.imp ha hb
    · exact step w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem old)) hit

theorem raw_required (c : Fin 4) {k S} (run : Cone ans k S)
    (bank : ∀ w∈S, ∃ j, w=lab c j) (which : Bool) : vtx (axis c which)∈S := by
  classical
  let v := axis c which
  have data : ∀ (c : Fin 4) (which : Bool), let t := axis c which
      ans (hi t)=true ∧ ans (lo t)=false ∧
      ∀ j : Fin 13, j.val≠t.val → lab c j (hi t)=true → lab c j (lo t)=true := by decide +kernel
  obtain ⟨one,zero,other⟩ := data c which
  by_contra absent
  have contradiction := ordered run (hi v) (lo v) (by
    intro w hw on
    obtain ⟨j,rfl⟩ := bank w hw
    apply other j _ on
    intro equal
    have bound : j.val<9 := by rw [equal]; exact v.isLt
    have same : lab c j=vtx v := by
      simp only [lab,dif_pos bound]
      exact congrArg vtx (Fin.ext equal)
    exact absent (same ▸ hw)) one
  exact Bool.false_ne_true (zero.symm.trans contradiction)

private theorem free_build {α β : Type} {fs ws : List (Wire α)} {n : Nat} (b : Build fs n ws)
    (f : β→α) (e : β) (seed : List (Wire β))
    (known : ∀ v∈fs, norm e (cut f v)∈seed) :
    ∃ ys, Free seed n ys ∧ ∀ w∈ws,norm e (cut f w)∈ys := by
  induction b with
  | start => exact ⟨seed,Free.start,known⟩
  | @gate k w before d a b ha hb ih =>
    obtain ⟨vs,run,hold⟩ := ih
    let c := normalizedKind d (a (f e)) (b (f e))
    let prog := Free.binary run c (hold a ha) (hold b hb)
    refine ⟨_,prog,?_⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl | old
    · change norm e (fun r => base d ((cut f a) r) ((cut f b) r)) ∈ _
      rw [normalize_binary]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hold z old)

theorem price {n ws} (h : Build bank7 n ws) (out : ans7∈ws) (L : SignedLower) : 11≤n := by
  have known : ∀ a∈bank7, norm (0:SmallInput) (cut id a)∈vertices7 := by
    intro a mem
    rcases List.mem_append.mp mem with raw|cc
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp raw
      have z : raw7 i 0=false := by simp [raw7]
      have same : norm (0:SmallInput) (cut id (raw7 i))=raw7 i := by
        funext r; simp [cut,CoThetaFreeCore.norm,phase,z]
      exact same ▸ List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at cc
      rcases cc with rfl|rfl <;> exact List.mem_cons_self
  obtain ⟨vs,free,hold⟩ := free_build h id 0 vertices7 known
  have z : ans7 0=false := by decide
  have same : norm (0:SmallInput) (cut id ans7)=ans7 := by
    funext r; simp [cut,CoThetaFreeCore.norm,phase,z]
  exact L free (same ▸ hold _ out)

theorem negative_unused (L : SignedLower) (c : Fin 4) {k S} (run : Cone ans k S)
    (bank : ∀ w∈S, ∃ j, w=lab c j) (small : k≤13) : neg c∉S := by
  classical
  intro negative
  have p := raw_required c run bank true
  have q := raw_required c run bank false
  change vtx (marked c)∈S at p
  change vtx (mate c)∈S at q
  have zeros : ∀ (c : Fin 4) (r : SmallInput), vtx (marked c) (slice c r)=false ∧ vtx (mate c) (slice c r)=false ∧ neg c (slice c r)=true := by decide +kernel
  have answer : cut (slice c) ans=ans7 := funext (fun r => (slice7_values (![0,2,0,2] c) r).1)
  have nc : ¬ Constant (cut (slice c) ans) := by
    rw [answer]; rintro ⟨b,e⟩
    have h := congrFun e (0:SmallInput)
    have h' := congrFun e (5:SmallInput)
    have zz : ans7 0=false := by decide
    have tt : ans7 5=true := by decide
    change ans7 _=b at h h'
    rw [zz] at h
    rw [tt] at h'
    exact Bool.false_ne_true (h.trans h'.symm)
  have shape : ∀ (c : Fin 4) (j : Fin 13),
      (∃ b : Bool, ∀ r : SmallInput, lab c j (slice c r)=b) ∨
      ∃ i : Fin 7, ∀ r : SmallInput, lab c j (slice c r)=raw7 i r := by decide +kernel
  have cs (b : Bool) : con b∈bank7 := by cases b <;> simp [bank7]
  have available (w) (hw : w∈S) : cut (slice c) w∈bank7 := by
    obtain ⟨j,rfl⟩ := bank w hw
    rcases shape c j with ⟨b,e⟩|⟨i,e⟩
    · have eq : cut (slice c) (lab c j)=con b := funext e
      exact eq ▸ cs b
    · have eq : cut (slice c) (lab c j)=raw7 i := funext e
      rw [eq]; exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  obtain ⟨m,ys,build,hit,budget⟩ := projected run (slice c) nc (Build.start (raw:=bank7)) cs available
  rw [answer] at hit
  have low := price build hit L
  let A := S.filter (fun w => Constant (cut (slice c) w))
  have pA : vtx (marked c)∈A := Finset.mem_filter.mpr ⟨p,false,funext (fun r => (zeros c r).1)⟩
  have qA : vtx (mate c)∈A := Finset.mem_filter.mpr ⟨q,false,funext (fun r => (zeros c r).2.1)⟩
  have nA : neg c∈A := Finset.mem_filter.mpr ⟨negative,true,funext (fun r => (zeros c r).2.2)⟩
  have neq : marked c≠mate c := (show ∀ c : Fin 4, marked c≠mate c by decide) c
  have hm (i : Fin 9) : vtx i≠neg c := by
    intro e
    have z := congrFun e (row 0)
    exact (show ∀ (i : Fin 9) (j : Fin 4), vtx i (row 0)≠neg j (row 0) by decide) i c z
  have three : ({vtx (marked c),vtx (mate c),neg c} : Finset (Wire Input)) ⊆ A := by
    intro w hw
    simp only [Finset.mem_insert,Finset.mem_singleton] at hw
    rcases hw with rfl|rfl|rfl <;> assumption
  have cnt := Finset.card_le_card three
  have gain : 3≤losses (slice c) S := by
    change 3≤A.card
    simpa [Finset.card_insert_of_notMem,distinct_inputs neq,hm] using cnt
  omega
#print axioms CoMask3024.negative_unused
end
end CoMask3024
