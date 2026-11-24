import PEqualNP.CoRootless3825

namespace CoMaskedNot3825
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CoNonredundant3825 CoNearReaders3825 CoRootless3825

def step (xs : List Bool) (g : Gate) := xs++[g.op.eval (g.inputs.map fun j => xs.getD j false)]

def dominatesAway (v : ℕ) (a b : List Bool) : Prop :=
  ∀ j,j≠v → a.getD j false=true → b.getD j false=true

/-- All suffix gates are positive and avoid raw v, except optional NOT(v) gates.
    This allows arbitrary fanout and repeated NOT(v) occurrences. -/
def allowed (v : ℕ) (g : Gate) : Prop :=
  (g.op=.not ∧ g.inputs=[v]) ∨ ((g.op=.and ∨ g.op=.or) ∧ v∉g.inputs)

private theorem gate_up {v : ℕ} {a b : List Bool} (away : dominatesAway v a b)
    (large : a.getD v false=true) {g : Gate} (ok : allowed v g) :
    g.op.eval (g.inputs.map (fun j => a.getD j false))=true →
    g.op.eval (g.inputs.map (fun j => b.getD j false))=true := by
  rcases ok with ⟨op,pins⟩|⟨and_or,none⟩
  · simp only [List.getD_eq_getElem?_getD] at large
    simp [op,pins,GateOp.eval,large]
  · have order (j) (hj : j∈g.inputs) : a.getD j false=true → b.getD j false=true :=
      away j (fun eq => none (eq ▸ hj))
    rcases and_or with op|op
    · simp only [op,GateOp.eval,List.all_eq_true,List.mem_map,Function.id_def]
      intro yes q hq
      obtain ⟨j,hj,rfl⟩ := hq
      exact order j hj (yes _ ⟨j,hj,rfl⟩)
    · simp only [op,GateOp.eval,List.any_eq_true,List.mem_map,Function.id_def]
      rintro ⟨q,⟨j,hj,rfl⟩,on⟩
      exact ⟨_,⟨j,hj,rfl⟩,order j hj on⟩

private theorem append_bit {v : ℕ} {a b : List Bool} {x y : Bool}
    (len : a.length=b.length) (away : dominatesAway v a b) (fresh : x=true→y=true) :
    dominatesAway v (a++[x]) (b++[y]) := by
  intro j ne yes
  by_cases low : j < a.length
  · have low' : j < b.length := len ▸ low
    have lhs : (a++[x]).getD j false=a.getD j false := by
      simp [List.getD_eq_getElem?_getD,List.getElem?_append_left low]
    have rhs : (b++[y]).getD j false=b.getD j false := by
      simp [List.getD_eq_getElem?_getD,List.getElem?_append_left low']
    exact rhs.trans (away j ne (lhs.symm.trans yes))
  · have ha : a.length ≤ j := by omega
    have hb : b.length ≤ j := by omega
    rw [List.getD_eq_getElem?_getD,List.getElem?_append_right ha] at yes
    rw [List.getD_eq_getElem?_getD,List.getElem?_append_right hb,←len]
    cases r : j-a.length with
    | zero => simpa [r] using fresh (by simpa [r] using yes)
    | succ t => simp [r,List.getD_eq_getElem?_getD] at yes

theorem suffix_away {v : ℕ} (gs : List Gate) {a b : List Bool} (len : a.length=b.length)
    (valid : v < a.length) (large : a.getD v false=true) (away : dominatesAway v a b)
    (ok : ∀ g∈gs,allowed v g) :
    dominatesAway v (gs.foldl step a) (gs.foldl step b) := by
  induction gs generalizing a b with
  | nil => exact away
  | cons g gs ih =>
    have good := gate_up away large (ok g (by simp))
    have hold : (step a g).getD v false=a.getD v false := by
      simp [step,List.getD_eq_getElem?_getD,List.getElem?_append_left valid]
    exact ih (a:=step a g) (b:=step b g) (by simp [step,len]) (by simp [step]; omega)
      (hold.trans large) (append_bit len away good) (fun t ht => ok t (by simp [ht]))

def singleton (v : Fin 9) (i : Fin 9) := decide (i=v)
def mate (v : Fin 9) : Fin 9 := if v=0 then 1 else 0
def hiBank := List.ofFn (edgePair 0 1) ++ [true]
def loBank (v : Fin 9) := List.ofFn (singleton (mate v)) ++ [true]

private theorem banks (v : Fin 9) (endpoint : v=0 ∨ v=1) : dominatesAway v.val hiBank (loBank v) := by
  intro j ne val
  by_cases bound : j < 10
  · rcases endpoint with rfl|rfl <;> interval_cases j <;> first | contradiction | rfl | decide +revert
  · have beyond : hiBank.length ≤ j := by change 10 ≤ j; omega
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none beyond] at val

theorem endpoint_second_not {C : Circuit} {h : Gate} {gs : List Gate}
    (v : Fin 9) (endpoint : v=0 ∨ v=1) (layout : C.gates=h::gs)
    (head : h=⟨.or,[0,1]⟩ ∨ h=⟨.or,[1,0]⟩)
    (ok : ∀ g∈gs,allowed v.val g) :
    circuitFun 9 C≠graph := by
  intro correct
  have out := not_raw correct v
  have bh : hiBank.length=(loBank v).length := by simp [hiBank,loBank]
  have vv : v.val < hiBank.length := by change v.val < 10; have := v.isLt; omega
  have on : hiBank.getD v.val false=true := by rcases endpoint with rfl|rfl <;> decide
  have compare := suffix_away gs bh vv on (banks v endpoint) ok
  have a : C.wires (List.ofFn (edgePair 0 1))=gs.foldl step hiBank := by
    rcases head with rfl|rfl <;> simp only [Circuit.wires,layout,List.foldl_cons] <;> rfl
  have b : C.wires (List.ofFn (singleton (mate v)))=gs.foldl step (loBank v) := by
    rcases head with rfl|rfl <;> rcases endpoint with rfl|rfl <;>
      simp only [Circuit.wires,layout,List.foldl_cons] <;> rfl
  have apos : (C.wires (List.ofFn (edgePair 0 1))).getD C.output false=true :=
    (congrFun correct _).trans sample.1
  have zero : graph (singleton (mate v))=false := by
    rcases endpoint with rfl|rfl <;> decide +kernel
  have bneg : (C.wires (List.ofFn (singleton (mate v)))).getD C.output false=false :=
    (congrFun correct _).trans zero
  rw [a] at apos
  rw [b] at bneg
  exact Bool.false_ne_true (bneg.symm.trans (compare C.output out apos))

private theorem same_member {α : Type} {xs : List α} {a b : α} (ha : a∈xs) (hb : b∈xs)
    (cap : xs.length ≤ 1) : a=b := by
  rcases xs with _|⟨i,_|⟨j,t⟩⟩ <;> simp_all

/-- Purely physical two-count version: at most one NOT in the suffix, at most one
    further reader of the endpoint, and the observed intersection is exactly NOT(v). -/
theorem forced_no_raw_not {C : Circuit} {h : Gate} {gs : List Gate}
    (v : Fin 9) (endpoint : v=0 ∨ v=1) (layout : C.gates=h::gs)
    (fan : FanInTwo C) (head : h=⟨.or,[0,1]⟩ ∨ h=⟨.or,[1,0]⟩)
    (rawcap : (gs.filter (fun g => decide (v.val∈g.inputs))).length ≤ 1)
    (negcap : (gs.filter (fun g => g.op.eval [false])).length ≤ 1)
    (occurs : (⟨.not,[v.val]⟩ : Gate)∈gs) :
    circuitFun 9 C≠graph := by
  apply endpoint_second_not v endpoint layout head
  intro g hg
  let nv : Gate := ⟨.not,[v.val]⟩
  have memb : nv∈gs := occurs
  by_cases read : v.val∈g.inputs
  · have gmem : g∈gs.filter (fun t => decide (v.val∈t.inputs)) :=
      List.mem_filter.mpr ⟨hg,by simpa using read⟩
    have vmem : nv∈gs.filter (fun t => decide (v.val∈t.inputs)) :=
      List.mem_filter.mpr ⟨memb,by simp [nv]⟩
    have e := same_member gmem vmem rawcap
    subst g
    exact Or.inl ⟨rfl,rfl⟩
  · have ops := (fan g (by rw [layout]; exact List.mem_cons_of_mem _ hg)).1
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops
    rcases ops with A|O|N
    · exact Or.inr ⟨Or.inl A,read⟩
    · exact Or.inr ⟨Or.inr O,read⟩
    · have gmem : g∈gs.filter (fun t => t.op.eval [false]) :=
        List.mem_filter.mpr ⟨hg,by simp [N,GateOp.eval]⟩
      have vmem : nv∈gs.filter (fun t => t.op.eval [false]) :=
        List.mem_filter.mpr ⟨memb,rfl⟩
      have e := same_member gmem vmem negcap
      subst g
      exact Or.inl ⟨rfl,rfl⟩

#print axioms forced_no_raw_not
end CoMaskedNot3825
