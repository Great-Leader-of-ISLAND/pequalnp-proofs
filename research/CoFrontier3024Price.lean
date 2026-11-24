import PEqualNP.CoAO3143Restriction
import PEqualNP.CoPaid3143
import PEqualNP.CoThetaCuts3024

namespace CoFrontier3024Price

open CoAO3143Restriction CoThetaNine CoThetaFreeCore

noncomputable section
local instance {α : Type} : DecidableEq (Wire α) := Classical.decEq _

def bank7 : List (Wire SmallInput) := List.ofFn raw7 ++ [con false,con true]

theorem keeps_raw {α : Type} {raw pool : List (Wire α)} {h : Nat} (run : Free raw h pool) :
    ∀ w∈raw,w∈pool := by
  induction run with
  | start => exact fun w hw => hw
  | binary pre k ha hb ih => exact fun w hw => List.mem_cons_of_mem _ (ih w hw)

private theorem normalize_ao {α : Type} (e : α) {raw ws : List (Wire α)} {n}
    (run : Build raw n ws) {seed pool : List (Wire α)} {h}
    (before : Free seed h pool) (known : ∀ w∈raw,norm e w∈pool) :
    ∃ ys, Free seed (h+n) ys ∧ ∀ w∈ws,norm e w∈ys := by
  induction run with
  | start => exact ⟨pool,by simpa using before,known⟩
  | @gate k ws pre d a b ha hb ih =>
    obtain ⟨ys,free,old⟩ := ih
    let t := normalizedKind d (a e) (b e)
    have step := Free.binary free t (old a ha) (old b hb)
    refine ⟨_,by simpa [Nat.add_assoc] using step,?_⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl|prev
    · change norm e (fun r => base d (a r) (b r))∈_
      rw [normalize_binary]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (old w prev)

theorem answer_nonconstant : ¬ Constant ans7 := by
  rintro ⟨b,eq⟩
  have a := congrFun eq (0:SmallInput)
  have c := congrFun eq (5:SmallInput)
  have f : ans7 0=false := by decide
  have t : ans7 5=true := by decide
  change ans7 _=b at a c
  rw [f] at a
  rw [t] at c
  exact Bool.false_ne_true (a.trans c.symm)

private theorem norm_answer : norm (0:SmallInput) ans7=ans7 := by
  have zero : ans7 0=false := by decide
  funext i
  simp [CoThetaFreeCore.norm,CoThetaFreeCore.phase,zero]

/-- The paid prefix may already hold the normalized negation of a raw signal. Each
    live source whose restriction is constant saves one further suffix operation. -/
theorem frontier_signed {α : Type} (L : SignedLower) {out : Wire α} {k S}
    (run : Cone out k S) (lift : SmallInput→α) (label : cut lift out=ans7)
    {h pool} (before : Free vertices7 h pool)
    (hold : ∀ w∈S,norm (0:SmallInput) (cut lift w)∈pool) :
    11 + losses lift S ≤ h+k := by
  classical
  let raw : List (Wire SmallInput) := con false::con true::S.toList.map (cut lift)
  have nc : ¬ Constant (cut lift out) := by
    rw [label]
    exact answer_nonconstant
  have cs (b : Bool) : con b∈raw := by cases b <;> simp [raw]
  have entry (w) (hw : w∈S) : cut lift w∈raw := by
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact List.mem_map_of_mem (by simpa using hw)
  obtain ⟨m,ys,proj,sol,budget⟩ := projected run lift nc (Build.start (raw:=raw)) cs entry
  have z : absentBit∈pool := keeps_raw before _ List.mem_cons_self
  have start (w) (hw : w∈raw) : norm (0:SmallInput) w∈pool := by
    rcases List.mem_cons.mp hw with rfl|hw
    · exact z
    rcases List.mem_cons.mp hw with rfl|hw
    · exact z
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
    exact hold v (by simpa using hv)
  obtain ⟨zs,free,keep⟩ := normalize_ao (0:SmallInput) proj before start
  have outKnown := keep _ sol
  rw [label,norm_answer] at outKnown
  have bound := L free outKnown
  omega

private theorem known_bank (w : Wire SmallInput) (hw : w∈bank7) : norm (0:SmallInput) w∈vertices7 := by
  rcases List.mem_append.mp hw with bits|cs
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp bits
    have v : raw7 i 0=false := by simp [raw7]
    have e : norm (0:SmallInput) (raw7 i)=raw7 i := by funext r; simp [CoThetaFreeCore.norm,CoThetaFreeCore.phase,v]
    rw [e]
    exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at cs
    rcases cs with rfl|rfl <;> exact List.mem_cons_self

theorem frontier {α : Type} (L : SignedLower) {out : Wire α} {k S}
    (run : Cone out k S) (lift : SmallInput→α) (label : cut lift out=ans7)
    {h pool} (before : Build bank7 h pool) (hold : ∀ w∈S,cut lift w∈pool) :
    11 + losses lift S ≤ h+k := by
  obtain ⟨ys,free,known⟩ := normalize_ao (0:SmallInput) before (Free.start (raw:=vertices7)) known_bank
  have bound := frontier_signed L run lift label free (fun w hw => known _ (hold w hw))
  simpa using bound

theorem nine_labels : ∀ (j : Fin 9) (r : SmallInput),ans (CoThetaCuts3024.plant j r)=ans7 r :=
  CoThetaCuts3024.label

theorem nine_signed (L : SignedLower) (j : Fin 9) {k S} (run : Cone ans k S)
    {h pool} (before : Free vertices7 h pool)
    (hold : ∀ w∈S,norm (0:SmallInput) (cut (CoThetaCuts3024.plant j) w)∈pool) :
    11 + losses (CoThetaCuts3024.plant j) S ≤ h+k :=
  frontier_signed L run _ (funext (nine_labels j)) before hold

/-- A constant or a previously available operand incurs no gate on this slice. -/
def Reusable (z a b : Wire SmallInput) : Prop := Constant z ∨ z=a ∨ z=b

theorem collapsed (d : Bool) (a b : Wire SmallInput) (hc : Constant a ∨ Constant b) :
    Reusable (op d a b) a b := by
  rcases hc with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases d <;> cases v
    · exact Or.inl ⟨false,by funext r; simp [op,con]⟩
    · exact Or.inr (Or.inr (by funext r; simp [op,con]))
    · exact Or.inr (Or.inr (by funext r; simp [op,con]))
    · exact Or.inl ⟨true,by funext r; simp [op,con]⟩
  · cases d <;> cases v
    · exact Or.inl ⟨false,by funext r; simp [op,con]⟩
    · exact Or.inr (Or.inl (by funext r; simp [op,con]))
    · exact Or.inr (Or.inl (by funext r; simp [op,con]))
    · exact Or.inl ⟨true,by funext r; simp [op,con]⟩

theorem free_step {h pool} (pre : Free vertices7 h pool) {z a b : Wire SmallInput}
    (ha : norm 0 a∈pool) (hb : norm 0 b∈pool) (hz : Reusable z a b) : norm 0 z∈pool := by
  rcases hz with ⟨v,rfl⟩ | rfl | rfl
  · cases v <;> exact keeps_raw pre _ List.mem_cons_self
  · exact ha
  · exact hb

theorem paid_step {h pool} (pre : Free vertices7 h pool) (d : Bool) {a b : Wire SmallInput}
    (ha : norm 0 a∈pool) (hb : norm 0 b∈pool) :
    ∃ ys,Free vertices7 (h+1) ys ∧ (∀ w∈pool,w∈ys) ∧ norm 0 (op d a b)∈ys := by
  let t := normalizedKind d (a 0) (b 0)
  refine ⟨_,Free.binary pre t ha hb,fun w hw => List.mem_cons_of_mem _ hw,?_⟩
  change norm 0 (fun r => base d (a r) (b r))∈_
  rw [normalize_binary]
  exact List.mem_cons_self

theorem neg_known {a : Wire SmallInput} {pool : List (Wire SmallInput)} (ha : norm 0 a∈pool) :
    norm 0 (fun r => !(a r))∈pool := by rw [normalize_unary]; exact ha

#print axioms CoFrontier3024Price.frontier_signed
#print axioms CoFrontier3024Price.nine_signed

end
end CoFrontier3024Price
