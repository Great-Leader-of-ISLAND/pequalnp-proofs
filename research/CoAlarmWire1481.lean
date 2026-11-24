import PEqualNP.CoFormula1963Physical
import PEqualNP.CoAlarmDerivative1481

namespace CoAlarmWire1481
open PEqualNP.CircuitLowerBounds CoFormula1963Protocol CoFormula1963Geometry
open CoFormula1963Circuit CoAlarmDerivative1481
abbrev X := V ⊕ V
abbrev Pair := Bool × Bool

def info (row : X → Bool) (v : X) (t : Term) : Pair := (val row t,match t with
  | .fixed _ => false | .tree f => alarm row v f)

def product (d : Bool) (a b : Pair) : Pair :=
    if d then (a.1 && b.1,(a.1 && b.2) || (a.2 && b.1))
    else (a.1 || b.1,a.2 || b.2)

def clean : Term → Prop | .fixed a => a=false | .tree _ => True

theorem combining (row : X → Bool) (v : X) (d : Bool) (a b : Term)
    (ha : clean a) (hb : clean b) :
    clean (combine d a b) ∧ info row v (combine d a b)=product d (info row v a) (info row v b) := by
  cases a with
  | fixed x =>
    change x=false at ha
    subst x
    cases b with
    | fixed y => change y=false at hb;subst y;cases d <;> exact ⟨rfl,rfl⟩
    | tree f => cases d <;> simp [clean,combine,info,val,product]
  | tree f =>
    cases b with
    | fixed y =>
      change y=false at hb
      subst y
      cases d <;> simp [clean,combine,info,val,product]
    | tree g => cases d <;> simp [clean,combine,info,val,Expr.eval,alarm,product]

def jetStep (w : List Pair) (g : Gate) : Pair :=
    product (andFlag g.op) (w.getD (g.inputs.getD 0 0) (false,false)) (w.getD (g.inputs.getD 1 0) (false,false))

def advance (gs : List Gate) (w : List Pair) := gs.foldl (fun ws g => ws++[jetStep ws g]) w

theorem read_clean (w : List Term) (h : ∀ t∈w,clean t) (i : Nat) : clean (w.getD i (.fixed false)) := by
  induction w generalizing i with
  | nil => rfl
  | cons t ts ih =>
    cases i with
    | zero => exact h t (by simp)
    | succ i => exact ih (fun u hu => h u (by simp [hu])) i

theorem step_info (row : X → Bool) (v : X) (g : Gate) (w : List Term)
    (hh : ∀ t∈w,clean t) {a b : Nat} (pins : g.inputs=[a,b]) :
    clean (build w g) ∧ info row v (build w g)=jetStep (w.map (info row v)) g := by
  have core := combining row v (andFlag g.op) _ _ (read_clean w hh a) (read_clean w hh b)
  have ea : (w.map (info row v)).getD a (false,false)=info row v (w.getD a (.fixed false)) :=
    map_get (info row v) (.fixed false) w a
  have eb : (w.map (info row v)).getD b (false,false)=info row v (w.getD b (.fixed false)) :=
    map_get (info row v) (.fixed false) w b
  simpa only [build,jetStep,pins,List.getD_cons_zero,List.getD_cons_succ,ea,eb] using core

theorem trace_info (row : X → Bool) (v : X) (gs : List Gate)
    (binary : ∀ g∈gs, ∃ a b : Nat,g.inputs=[a,b]) (w : List Term) (hh : ∀ t∈w,clean t) :
    (run gs w).map (info row v)=advance gs (w.map (info row v)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨a,b,pins⟩ := binary g (by simp)
    obtain ⟨good,eq⟩ := step_info row v g w hh pins
    change (run gs (w++[build w g])).map (info row v)=advance gs ((w.map (info row v))++[jetStep (w.map (info row v)) g])
    rw [ih (fun z hz => binary z (by simp [hz])) _ (by
      intro t ht
      rcases List.mem_append.mp ht with ht|ht
      · exact hh t ht
      · simp only [List.mem_singleton] at ht
        subst t
        exact good)]
    simp [eq]

def physical (C : Circuit) (row : X → Bool) (v : X) : Bool :=
  ((advance C.gates (initial.map (info row v))).getD C.output (false,false)).2

theorem output_flag (C : Circuit) (row : X → Bool) (v : X)
    (binary : ∀ g∈C.gates,∃ a b : Nat,g.inputs=[a,b]) :
    (info row v ((run C.gates initial).getD C.output (.fixed false))).2=physical C row v := by
  have all : ∀ t∈initial,clean t := by simp [initial,clean,List.mem_ofFn]
  have eq := trace_info row v C.gates binary initial all
  unfold physical
  rw [←eq]
  exact congrArg Prod.snd (map_get (info row v) (.fixed false) (run C.gates initial) C.output).symm

#print axioms output_flag
end CoAlarmWire1481
