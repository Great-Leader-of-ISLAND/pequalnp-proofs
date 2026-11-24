import PEqualNP.CoPetersenRestrictReaders

namespace Co1940Slice
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Research.PetersenRestrict

def goal7 (x : Fin 7→Bool) : Bool :=
  (x 0 && x 2) || (x 2 && x 1) || (x 0 && x 3) || (x 3 && x 4) ||
  (x 4 && x 1) || (x 0 && x 5) || (x 5 && x 6) || (x 6 && x 1)
def goal9 (x : Fin 9→Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
def NoSupplied (j : Fin 7) : Prop := ∀ D : Circuit, D.size≤10 → FanInTwo D →
  ¬∀ x : Fin 7→Bool, D.eval (List.ofFn x ++ [!(x j)])=goal7 x

def signed (j : Fin 7) (x : Fin 7→Bool) : Fin 8→Bool := Fin.snoc x (!(x j))

theorem signed_list (j : Fin 7) (x : Fin 7→Bool) :
    List.ofFn (signed j x) = List.ofFn x ++ [!(x j)] := by
  rw [List.ofFn_succ']
  simp [signed,Fin.snoc]

theorem charge (noTail : ∀ j, NoSupplied j) (C : Circuit) (fan : FanInTwo C)
    (j : Fin 7) (refs : List Wire) (bounded : ∀ r∈refs, r.Bounded 8)
    (slots : Finset Nat) (ready : Ready slots refs)
    (correct : ∀ x : Fin 7→Bool, C.eval (substituted refs (signed j x))=goal7 x) :
    11 + directSavings slots C.gates ≤ C.size := by
  have notConstant : ∃ a b : Fin 8→Bool, C.eval (substituted refs a) ≠ C.eval (substituted refs b) := by
    refine ⟨signed j (fun _=>false),signed j (fun _=>true),?_⟩
    rw [correct,correct]
    decide
  obtain ⟨D,df,price,eq⟩ := specialize C fan refs bounded notConstant
  have lower : 11 ≤ D.size := by
    by_contra h
    apply noTail j D (by omega) df
    intro x
    have e := (eq (signed j x)).trans (correct x)
    simpa only [signed_list] using e
  have gain := scan_direct slots C.gates 8 refs ready
  omega

def port (p : Option (Fin 7)) : Wire := match p with | none => .fixed false | some k => .port k.val
def invPort (p : Option (Fin 7)) : Wire := match p with | none => .fixed true | some _ => .port 7

def map9 (j : Fin 6) : Fin 9 → Option (Fin 7) := match j.val with
  | 0 => ![none,some 3,some 0,some 2,none,some 6,some 4,some 5,some 1]
  | 1 => ![some 6,none,some 3,some 0,some 5,some 1,none,some 4,some 2]
  | 2 => ![some 1,some 6,none,some 3,some 4,some 2,some 5,none,some 0]
  | 3 => ![some 2,some 1,some 6,none,none,some 0,some 4,some 5,some 3]
  | 4 => ![some 0,some 2,some 1,some 6,some 5,some 3,none,some 4,none]
  | _ => ![some 3,some 0,some 2,some 1,some 4,none,some 5,none,some 6]

def plant (j : Fin 6) (x : Fin 7→Bool) (i : Fin 9) : Bool := (map9 j i).elim false x

theorem geom : ∀ (j : Fin 6) (x : Fin 7→Bool), goal9 (plant j x)=goal7 x := by decide +kernel

def refs (j : Fin 6) (b : Fin 9) : List Wire :=
  List.ofFn (fun i => port (map9 j i)) ++ [invPort (map9 j 0),invPort (map9 j b)]

theorem refs_bounded (j : Fin 6) (b : Fin 9) : ∀ w∈refs j b,w.Bounded 8 := by
  intro w hw
  rcases List.mem_append.mp hw with h|h
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
    cases e : map9 j i with
    | none => trivial
    | some k => exact Nat.lt_trans k.isLt (by decide)
  · simp only [List.mem_cons,List.mem_singleton] at h
    rcases h with rfl|rfl
    · cases e : map9 j 0 <;> decide
    · cases e : map9 j b <;> decide

private theorem eval_raw (j : Fin 7) (x : Fin 7→Bool) (k : Fin 7) :
    read (List.ofFn (signed j x)) k.val=x k := by
  rw [signed_list]
  simp only [read,List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simpa using k.isLt : k.val<(List.ofFn x).length),
    List.getElem?_ofFn,k.isLt,reduceDIte,Option.getD_some]

private theorem eval_last (j : Fin 7) (x : Fin 7→Bool) :
    read (List.ofFn (signed j x)) 7=!(x j) := by
  rw [signed_list]
  simp [read,List.getD_eq_getElem?_getD,List.getElem?_append]

private theorem inv_val (i : Option (Fin 7)) (j : Fin 7)
    (ok : ∀ k, i=some k → k=j) (x : Fin 7→Bool) :
    (invPort i).val (read (List.ofFn (signed j x))) = !(i.elim false x) := by
  cases i with
  | none => rfl
  | some k =>
    have e := ok k rfl
    subst k
    exact eval_last j x

theorem actual_refs (j : Fin 6) (b : Fin 9) (w : Fin 7)
    (aOK : ∀ k, map9 j 0=some k → k=w) (bOK : ∀ k, map9 j b=some k → k=w)
    (x : Fin 7→Bool) :
    substituted (refs j b) (signed w x) = List.ofFn (plant j x) ++ [!(plant j x 0),!(plant j x b)] := by
  have rawEq (i : Fin 9) :
      (port (map9 j i)).val (read (List.ofFn (signed w x)))=plant j x i := by
    simp only [plant]
    cases e : map9 j i with
    | none => rfl
    | some k => exact eval_raw w x k
  simp only [substituted,refs,List.map_append,List.map_cons,List.map_nil,List.map_ofFn]
  simp only [Function.comp_def,rawEq,inv_val _ _ aOK x,inv_val _ _ bOK x,plant]

theorem distinct_sources_slice (noTail : ∀ j, NoSupplied j) (C : Circuit) (fan : FanInTwo C)
    (b : Fin 9) (correct : ∀ x, C.eval (List.ofFn x ++ [!(x 0),!(x b)])=goal9 x)
    (j : Fin 6) (w : Fin 7) (aOK : ∀ k, map9 j 0=some k → k=w)
    (bOK : ∀ k, map9 j b=some k → k=w) (slots : Finset Nat) (ready : Ready slots (refs j b)) :
    11 + directSavings slots C.gates ≤ C.size := by
  apply charge noTail C fan w _ (refs_bounded j b) slots ready
  intro x
  rw [actual_refs j b w aOK bOK,correct,geom]

def fixedTag : Wire→Bool
  | .fixed _ => true
  | .port _ => false

def fixedSlots (rs : List Wire) : Finset Nat :=
  (Finset.range rs.length).filter (fun i => fixedTag (resolve rs i)=true)

theorem ready_fixed (rs : List Wire) : Ready (fixedSlots rs) rs := by
  intro i h
  obtain ⟨lt,flag⟩ := Finset.mem_filter.mp h
  refine ⟨Finset.mem_range.mp lt,?_⟩
  cases eq : resolve rs i with
  | fixed b => exact ⟨b,rfl⟩
  | port n => simp [eq,fixedTag] at flag

def survivor (j : Fin 6) (b : Fin 9) : Fin 7 :=
  ((map9 j 0).orElse (fun _ => map9 j b)).getD 0

theorem survivor_ok : ∀ (j : Fin 6) (b : Fin 9),
    (map9 j 0=none ∨ map9 j b=none ∨ b=0) →
    (∀ k, map9 j 0=some k → k=survivor j b) ∧
    (∀ k, map9 j b=some k → k=survivor j b) := by decide +kernel

theorem three_readers_exclude (noTail : ∀ j, NoSupplied j) (C : Circuit) (fan : FanInTwo C)
    (small : C.size≤13) (b : Fin 9) (j : Fin 6)
    (covers : map9 j 0=none ∨ map9 j b=none ∨ b=0)
    (three : 3 ≤ directSavings (fixedSlots (refs j b)) C.gates) :
    ¬∀ x, C.eval (List.ofFn x ++ [!(x 0),!(x b)])=goal9 x := by
  intro yes
  obtain ⟨aOK,bOK⟩ := survivor_ok j b covers
  have lower := distinct_sources_slice noTail C fan b yes j (survivor j b) aOK bOK _
    (ready_fixed (refs j b))
  omega

end Co1940Slice
