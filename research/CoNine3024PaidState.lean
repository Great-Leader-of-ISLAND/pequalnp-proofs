import PEqualNP.CoFrontier3024Counts
import PEqualNP.CoNine3024FixedMap
import PEqualNP.CoNine3024Rows

namespace CoNine3024PaidState
open CoNine3024 CoNine3024Rows CoNine3024Budget CoNine3024FixedMap CoThetaNine CoThetaFreeCore CoAO3143Restriction

noncomputable section
local instance {α : Type} : DecidableEq (Wire α) := Classical.decEq _
local instance (P : Prop) : Decidable P := Classical.propDecidable P

def digit (a : Atom) : Counts := flag maskWord a.full

theorem digit_bound (a : Atom) (j : Fin 9) : digit a j≤1 := flag_le _ _ _

theorem digit_correct (a : Atom) (j : Fin 9) :
    digit a j=1 ↔ Constant (cut (CoThetaCuts3024.plant j) (value a)) := flag_constant a.full j

private theorem digit_if (a : Atom) (j : Fin 9) :
    digit a j=if Constant (cut (CoThetaCuts3024.plant j) (value a)) then 1 else 0 := by
  by_cases h : Constant (cut (CoThetaCuts3024.plant j) (value a))
  · rw [if_pos h]
    exact (digit_correct a j).2 h
  · rw [if_neg h]
    have bound := digit_bound a j
    have neq : digit a j≠1 := fun e => h ((digit_correct a j).1 e)
    omega

theorem packed_good {p a} (g : Good p a) : a.fixed=pack (digit a) := by
  rw [g.fixed,←mask_table]
  exact fixedMask_pack _ _

/-- Each slice has a realizable prefix holding every current label. The nine
    budgets are represented individually and by the search's packed word. -/
def Accounts (s : State) (k : Nat) : Prop := ∃ c : Counts, s.spent=pack c ∧
  ∀ j : Fin 9, ∃ h pool,Free vertices7 h pool ∧ h+c j+k≤14 ∧
    ∀ w∈s.wires,norm 0 (cut (CoThetaCuts3024.plant j) (value w))∈pool

theorem safe_of_accounts (L : SignedLower) {p : Fin 11} {s : State} {k : Nat}
    (acc : Accounts s k) (good : ∀w∈s.wires,Good p w) (nd : (s.wires.map value).Nodup)
    {S : Finset (Wire Input)} (run : Cone ans k S) (images : (s.wires.map value).toFinset=S) : safe s=true := by
  obtain ⟨c,spent,proj⟩ := acc
  rw [←images] at run
  apply CoFrontier3024Counts.safe_semantic L s value c digit spent (fun w hw => packed_good (good w hw)) nd
    (fun j w _ => digit_if w j) run
  intro j
  obtain ⟨h,pool,pre,clock,hold⟩ := proj j
  refine ⟨h,pool,pre,clock,?_⟩
  intro v hv
  have hm : v∈s.wires.map value := by simpa using hv
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
  exact hold w hw

private theorem kept_old {s : State} {a b : Atom} (ha : a∈s.wires) (hb : b∈s.wires) (mask : Nat) :
    ∀w∈maskKeep a b mask ++ rest s a b,w∈s.wires := by
  intro w hw
  rcases List.mem_append.mp hw with hk|hr
  · rcases mask with _|(_|(_|n)) <;> simp [maskKeep] at hk <;> aesop
  · exact (List.mem_filter.mp hr).1

theorem advance (p : Fin 11) {k : Nat} {s : State} (acc : Accounts s (k+1))
    (a b : Atom) (ha : a∈s.wires) (hb : b∈s.wires) (ga : Good p a) (gb : Good p b)
    (d : Bool) (mask : Nat) : Accounts (child s a b (operation (geom p) d a b) (rest s a b) mask) k := by
  obtain ⟨c,spent,proj⟩ := acc
  refine ⟨fun j => c j+max (digit a j) (digit b j),
    child_spent s a b _ _ mask c _ _ spent (packed_good ga) (packed_good gb) (digit_bound a) (digit_bound b),?_⟩
  intro j
  obtain ⟨h,pool,pre,oldClock,hold⟩ := proj j
  let f := CoThetaCuts3024.plant j
  obtain ⟨n,ws,prog,pay,keep,z⟩ := CoFrontier3024Seed.advance pre d (cut f (value a)) (cut f (value b))
    (hold a ha) (hold b hb) _ _ (digit_bound a j) (digit_bound b j) (digit_correct a j) (digit_correct b j)
  refine ⟨n,ws,prog,by omega,?_⟩
  intro w hw
  rcases List.mem_cons.mp hw with rfl|old
  · rw [operation_value]
    exact z
  · exact keep _ (hold w (kept_old ha hb mask w old))

theorem initial_accounts (p : Fin 11) (useSeed : Bool) (k : Nat) (small : k≤13)
    (represented : ∀w∈(root p useSeed).wires,∃i : Fin 13,value w=CoAllRaw3024.label p i) :
    Accounts (root p useSeed) k := by
  let x := digit (rootAtom p 0)
  let y := digit (rootAtom p 2)
  refine ⟨fun j => max (x j) (y j),?_,?_⟩
  · change (rootAtom p 0).fixed ||| (rootAtom p 2).fixed = _
    rw [packed_good (root_good p 0),packed_good (root_good p 2)]
    exact pack_or x y (digit_bound _) (digit_bound _)
  · intro j
    let f := CoThetaCuts3024.plant j
    obtain ⟨ws,prog,hold⟩ := CoFrontier3024Seed.nine_initial j p
    have bit (i : Fin 9) : digit (rootAtom p i) j=1 ↔ Constant (cut f (vtx i)) := by
      rw [←raw_value p i]
      exact digit_correct _ _
    have xc : x j=1 ↔ Constant (cut f (vtx 0)) := bit 0
    have yc : y j=1 ↔ Constant (cut f (vtx 2)) := bit 2
    have xb : x j≤1 := digit_bound _ _
    have yb : y j≤1 := digit_bound _ _
    have pay : CoFrontier3024Seed.fee f+max (x j) (y j)=1 := by
      unfold CoFrontier3024Seed.fee
      split
      · rename_i ok
        rcases ok with h|h
        · have on := xc.mpr h
          omega
        · have on := yc.mpr h
          omega
      · rename_i neg
        have nx : x j≠1 := fun e => neg (Or.inl (xc.mp e))
        have ny : y j≠1 := fun e => neg (Or.inr (yc.mp e))
        omega
    refine ⟨_,ws,prog,?_,?_⟩
    · change CoFrontier3024Seed.fee f+max (x j) (y j)+k≤14
      omega
    · intro w hw
      obtain ⟨i,eq⟩ := represented w hw
      rw [eq]
      exact hold i

theorem seed_value (p : Fin 11) : value (seedAtom p)=CoAllRaw3024.seed := by
  change value (operation (geom p) true (rootAtom p 0) (rootAtom p 2))=_
  rw [operation_value,raw_value,raw_value] <;> rfl

private theorem value_negated (w : Truth) (pos neg : Cells) (fixed : Nat) :
    value ⟨~~~w,pos,neg,fixed⟩=(fun r => !(w.getLsbD r.val)) := by
  funext r
  simp [value,BitVec.getLsbD_not,r.isLt]

theorem inverse_value (p : Fin 11) (present : p.val≠10) :
    value (inverseAtom p)=CoAllRaw3024.inverse p := by
  by_cases bound : p.val<9
  · simp only [inverseAtom,CoAllRaw3024.inverse,dif_pos bound,value_negated]
    change (fun r => !(value (rootAtom p ⟨p.val,bound⟩) r))=_
    rw [raw_value]
  · have pn := p.isLt
    have nine : p.val=9 := by omega
    simp only [inverseAtom,CoAllRaw3024.inverse,dif_neg bound,if_pos nine,value_negated]
    change (fun r => !(value (seedAtom p) r))=_
    rw [seed_value]

theorem root_represented (p : Fin 11) (useSeed : Bool) :
    ∀w∈(root p useSeed).wires,∃i : Fin 13,value w=CoAllRaw3024.label p i := by
  intro w hw
  change w∈(List.ofFn (rootAtom p) ++ (if useSeed then [seedAtom p] else [])) ++
    (if p.val=10 then [] else [inverseAtom p]) at hw
  rcases List.mem_append.mp hw with left|right
  · rcases List.mem_append.mp left with raw|sd
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp raw
      refine ⟨⟨i.val,lt_trans i.isLt (by decide : 9<13)⟩,?_⟩
      simpa only [CoAllRaw3024.label,dif_pos i.isLt] using raw_value p i
    · cases useSeed with
      | false => simp at sd
      | true =>
        have e : w=seedAtom p := by simpa using sd
        exact ⟨9,by rw [e]; exact seed_value p⟩
  · by_cases pn : p.val=10
    · simp [pn] at right
    · have e : w=inverseAtom p := by simpa [pn] using right
      exact ⟨10,by rw [e]; exact inverse_value p pn⟩

theorem initial_ready (p : Fin 11) (useSeed : Bool) (k : Nat) (small : k≤13) :
    Accounts (root p useSeed) k := initial_accounts p useSeed k small (root_represented p useSeed)

#print axioms CoNine3024PaidState.initial_accounts
#print axioms CoNine3024PaidState.advance
#print axioms CoNine3024PaidState.safe_of_accounts
end
end CoNine3024PaidState
