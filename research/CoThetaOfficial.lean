import PEqualNP.Defs

namespace CoThetaFreeCore

def phase (sign bit : Bool) : Bool := if sign then !bit else bit

def base (join a b : Bool) : Bool := if join then a || b else a && b

inductive Kind where
  | conj | disj | leftOnly | rightOnly

def applyKind : Kind → Bool → Bool → Bool
  | .conj, a, b => a && b
  | .disj, a, b => a || b
  | .leftOnly, a, b => a && !b
  | .rightOnly, a, b => !a && b

def normalizedKind : Bool → Bool → Bool → Kind
  | false, false, false => .conj
  | false, false, true  => .leftOnly
  | false, true, false  => .rightOnly
  | false, true, true   => .disj
  | true, false, false  => .disj
  | true, false, true   => .rightOnly
  | true, true, false   => .leftOnly
  | true, true, true    => .conj

theorem normalization_table : ∀ join a0 b0 a b : Bool,
    phase (base join a0 b0) (base join a b) =
    applyKind (normalizedKind join a0 b0) (phase a0 a) (phase b0 b) := by decide

theorem inversion_table : ∀ a0 a : Bool, phase (!a0) (!a) = phase a0 a := by decide

variable {ρ : Type}

def norm (empty : ρ) (a : ρ → Bool) : ρ → Bool := fun i => phase (a empty) (a i)

theorem normalize_binary (empty : ρ) (join : Bool) (a b : ρ → Bool) :
    norm empty (fun i => base join (a i) (b i)) =
    fun i => applyKind (normalizedKind join (a empty) (b empty)) (norm empty a i) (norm empty b i) := by
  funext i
  exact normalization_table join (a empty) (b empty) (a i) (b i)

theorem normalize_unary (empty : ρ) (a : ρ → Bool) :
    norm empty (fun i => !(a i)) = norm empty a := by
  funext i
  exact inversion_table (a empty) (a i)

end CoThetaFreeCore

namespace CoThetaFreeCore

variable {ρ : Type}

/-- A straight-line program with an explicit count of its binary steps.
    Newly computed wires are prepended, and existing wires may be shared. -/
inductive Ordinary (raw : List (ρ → Bool)) : Nat → List (ρ → Bool) → Prop
  | start : Ordinary raw 0 raw
  | inv {n ws a} (pre : Ordinary raw n ws) (ha : a ∈ ws) :
      Ordinary raw n ((fun i => !(a i)) :: ws)
  | binary {n ws a b} (pre : Ordinary raw n ws) (join : Bool) (ha : a ∈ ws) (hb : b ∈ ws) :
      Ordinary raw (n+1) ((fun i => base join (a i) (b i)) :: ws)

inductive Free (raw : List (ρ → Bool)) : Nat → List (ρ → Bool) → Prop
  | start : Free raw 0 raw
  | binary {n ws a b} (pre : Free raw n ws) (kind : Kind) (ha : a ∈ ws) (hb : b ∈ ws) :
      Free raw (n+1) ((fun i => applyKind kind (a i) (b i)) :: ws)

theorem simulate_all_wires (empty : ρ) {raw ws : List (ρ → Bool)} {n : Nat}
    (run : Ordinary raw n ws) :
    ∃ ys, Free (raw.map (norm empty)) n ys ∧
          ∀ a ∈ ws, norm empty a ∈ ys := by
  induction run with
  | start =>
    exact ⟨_, Free.start, fun a ha => List.mem_map_of_mem ha⟩
  | @inv n ws a pre ha ih =>
    obtain ⟨ys,hy,old⟩ := ih
    refine ⟨ys,hy,?_⟩
    intro w hw
    rcases List.mem_cons.mp hw with eq | was
    · rw [eq,normalize_unary]
      exact old a ha
    · exact old w was
  | @binary n ws a b pre join ha hb ih =>
    obtain ⟨ys,hy,old⟩ := ih
    let kk := normalizedKind join (a empty) (b empty)
    have fresh := Free.binary hy kk (old a ha) (old b hb)
    refine ⟨_,fresh,?_⟩
    intro w hw
    rcases List.mem_cons.mp hw with eq | was
    · rw [eq,normalize_binary]
      simp [kk]
    · exact List.mem_cons_of_mem _ (old w was)

end CoThetaFreeCore

namespace CoThetaFreeCore

variable {ρ : Type}

def absentBit : ρ → Bool := fun _ => false
def ins {α : Type} (a : α) (U : α → Prop) : α → Prop := fun v => v = a ∨ U v

/-- Work backwards through a DAG, preserving only the distinct signals still
    needed. U may contain either of the two inputs, representing reuse. -/
inductive Live (goal : ρ → Bool) : Nat → ((ρ → Bool) → Prop) → Prop
  | stop : Live goal 0 (fun v => v=goal)
  | step {k U a b} (kind : Kind) (ab : a≠b)
      (ha : a≠absentBit) (hb : b≠absentBit)
      (fresh : ¬ins a (ins b U) (fun i => applyKind kind (a i) (b i)))
      (tail : Live goal k (ins (fun i => applyKind kind (a i) (b i)) U)) :
      Live goal (k+1) (ins a (ins b U))

private theorem same_result (kind : Kind) (a : ρ → Bool) :
    (fun i => applyKind kind (a i) (a i)) = a ∨
    (fun i => applyKind kind (a i) (a i)) = absentBit := by
  cases kind with
  | conj => left; funext i; cases a i <;> rfl
  | disj => left; funext i; cases a i <;> rfl
  | leftOnly => right; funext i; cases a i <;> rfl
  | rightOnly => right; funext i; cases a i <;> rfl

private theorem zero_left (kind : Kind) (b : ρ → Bool) :
    (fun i => applyKind kind false (b i)) = b ∨
    (fun i => applyKind kind false (b i)) = absentBit := by
  cases kind with
  | conj => right; rfl
  | disj => left; funext i; cases b i <;> rfl
  | leftOnly => right; rfl
  | rightOnly => left; funext i; cases b i <;> rfl

private theorem zero_right (kind : Kind) (a : ρ → Bool) :
    (fun i => applyKind kind (a i) false) = a ∨
    (fun i => applyKind kind (a i) false) = absentBit := by
  cases kind with
  | conj => right; funext i; cases a i <;> rfl
  | disj => left; funext i; cases a i <;> rfl
  | leftOnly => left; funext i; cases a i <;> rfl
  | rightOnly => right; funext i; cases a i <;> rfl

private theorem free_keeps_raw {raw ws : List (ρ → Bool)} {n : Nat}
    (run : Free raw n ws) {v} (h : v∈raw) : v∈ws := by
  induction run with
  | start => exact h
  | binary _ _ _ _ ih => exact List.mem_cons_of_mem _ ih

theorem rewind {raw ws : List (ρ → Bool)} {n : Nat} (run : Free raw n ws)
    (hz : absentBit∈raw) {goal : ρ → Bool} {k : Nat} {S : (ρ → Bool) → Prop}
    (needed : Live goal k S) (available : ∀ w, S w → w∈ws) :
    ∃ m T, m≤k+n ∧ Live goal m T ∧ ∀ w, T w → w∈raw := by
  classical
  induction run generalizing k S with
  | start => exact ⟨k,S,by omega,needed,available⟩
  | @binary n ws a b pre kind ha hb ih =>
    let z : ρ → Bool := fun i => applyKind kind (a i) (b i)
    have rawzero : absentBit∈ws := free_keeps_raw pre hz
    have values (w) (hw : S w) : w=z ∨ w∈ws := List.mem_cons.mp (available w hw)
    by_cases used : S z
    · by_cases old : z∈ws
      · obtain ⟨m,T,hm,ht,hsub⟩ := ih needed (fun w hw =>
          (values w hw).elim (fun e => e.symm ▸ old) id)
        exact ⟨m,T,by omega,ht,hsub⟩
      · let U : (ρ → Bool) → Prop := fun w => w≠z ∧ S w
        have eq : ins z U = S := by
          funext w
          apply propext
          constructor
          · intro hw
            rcases hw with h | h
            · exact h.symm ▸ used
            · exact h.2
          · intro hw
            by_cases e : w=z
            · exact Or.inl e
            · exact Or.inr ⟨e,hw⟩
        have memU (w) (hw : U w) : w∈ws := (values w hw.2).resolve_left hw.1
        have memAll (w) (hw : ins a (ins b U) w) : w∈ws := by
          rcases hw with e | e | hu
          · exact e.symm ▸ ha
          · exact e.symm ▸ hb
          · exact memU w hu
        have distinct : a≠b := by
          intro hab
          subst b
          rcases same_result kind a with e|e
          · exact old ((congrArg (fun v => v∈ws) e).mpr ha)
          · exact old ((congrArg (fun v => v∈ws) e).mpr rawzero)
        have nonA : a≠absentBit := by
          intro ea
          subst a
          rcases zero_left kind b with e|e
          · exact old ((congrArg (fun v => v∈ws) e).mpr hb)
          · exact old ((congrArg (fun v => v∈ws) e).mpr rawzero)
        have nonB : b≠absentBit := by
          intro eb
          subst b
          rcases zero_right kind a with e|e
          · exact old ((congrArg (fun v => v∈ws) e).mpr ha)
          · exact old ((congrArg (fun v => v∈ws) e).mpr rawzero)
        have nxt : Live goal (k+1) (ins a (ins b U)) :=
          Live.step kind distinct nonA nonB (fun bad => old (memAll z bad)) (eq.symm ▸ needed)
        obtain ⟨m,T,hm,ht,hsub⟩ := ih nxt memAll
        exact ⟨m,T,by omega,ht,hsub⟩
    · obtain ⟨m,T,hm,ht,hsub⟩ := ih needed (fun w hw =>
        (values w hw).resolve_left (fun e => used (e ▸ hw)))
      exact ⟨m,T,by omega,ht,hsub⟩

end CoThetaFreeCore

namespace CoThetaFreeCore

variable {ρ : Type}

theorem Live.separates {goal : ρ → Bool} {S k} (h : Live goal k S)
    (pos neg : ρ) (different : goal pos≠goal neg) :
    ∃ w, S w ∧ w pos≠w neg := by
  induction h with
  | stop => exact ⟨goal,rfl,different⟩
  | @step n U a b kind hab ha hb hf tail ih =>
    obtain ⟨w,hw,diff⟩ := ih
    rcases hw with eq | inU
    · subst w
      by_cases ea : a pos=a neg
      · refine ⟨b,Or.inr (Or.inl rfl),?_⟩
        intro eb
        apply diff
        change applyKind kind (a pos) (b pos) = applyKind kind (a neg) (b neg)
        rw [ea,eb]
      · exact ⟨a,Or.inl rfl,ea⟩
    · exact ⟨w,Or.inr (Or.inr inU),diff⟩

private def eraseOnce {α : Type} [DecidableEq α] (v : α) : List α → List α
  | [] => []
  | x::xs => if x=v then xs else x::eraseOnce v xs

private theorem erase_len {α : Type} [DecidableEq α] (v : α) (xs : List α) (h : v∈xs) :
    (eraseOnce v xs).length+1=xs.length := by
  induction xs with
  | nil => simp at h
  | cons a l ih =>
    by_cases e : a=v
    · simp [eraseOnce,e]
    · have hit : v∈l := (List.mem_cons.mp h).resolve_left (Ne.symm e)
      have hlen := ih hit
      simp [eraseOnce,e]
      omega

private theorem erase_preserves {α : Type} [DecidableEq α] {v w : α} (hw : w≠v)
    (xs : List α) (hin : w∈xs) : w∈eraseOnce v xs := by
  induction xs with
  | nil => simp at hin
  | cons a l ih =>
    by_cases e : a=v
    · subst a
      simpa [eraseOnce] using (List.mem_cons.mp hin).resolve_left hw
    · simp only [eraseOnce,if_neg e,List.mem_cons]
      rcases List.mem_cons.mp hin with eq | old
      · exact Or.inl eq
      · exact Or.inr (ih old)

theorem Live.width_cover {goal : ρ → Bool} {S k} (h : Live goal k S) :
    ∃ xs : List (ρ→Bool), xs.length≤k+1 ∧ ∀ w, S w → w∈xs := by
  classical
  induction h with
  | stop =>
    refine ⟨[goal],by simp,?_⟩
    intro w eq
    change w=goal at eq
    subst w
    simp
  | @step n U a b kind hab ha hb fresh tail ih =>
    let z : ρ → Bool := fun i => applyKind kind (a i) (b i)
    obtain ⟨xs,len,sub⟩ := ih
    have inside : z∈xs := sub z (Or.inl rfl)
    have reduced := erase_len z xs inside
    refine ⟨a::b::eraseOnce z xs,?_,?_⟩
    · simp only [List.length_cons]
      omega
    · intro w hw
      rcases hw with eq | eq | hu
      · simp [eq]
      · simp [eq]
      · have ne : w≠z := by
          intro eq
          apply fresh
          exact Or.inr (Or.inr ((congrArg U eq).mp hu))
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (erase_preserves ne xs (sub w (Or.inr hu))))

end CoThetaFreeCore

namespace CoThetaFreeCore

def primary {ι : Type} (j : ι) (x : ι → Bool) := x j

theorem necessary_primary {ι : Type} {goal : (ι → Bool) → Bool} {S k}
    (run : Live goal k S) (j : ι)
    (inputs : ∀ w, S w → w=absentBit ∨ ∃ i, w=primary i)
    (sens : ∃ p n, goal p≠goal n ∧ ∀ i, i≠j → p i=n i) :
    S (primary j) := by
  obtain ⟨p,n,diff,rest⟩ := sens
  obtain ⟨wire,hw,dis⟩ := run.separates p n diff
  rcases inputs wire hw with c | ⟨i,c⟩
  · subst wire
    exact (dis rfl).elim
  · subst wire
    by_cases eq : i=j
    · exact eq ▸ hw
    · exact (dis (rest i eq)).elim

def theta (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 3 && x 4) ||
  (x 1 && x 4) || (x 0 && x 5) || (x 5 && x 6) || (x 1 && x 6)

def neigh (i : Fin 7) : Fin 7 := match i.val with
  | 0 => 2
  | 1 => 2
  | 2 => 0
  | 3 => 0
  | 4 => 1
  | 5 => 0
  | _ => 1

def single (j : Fin 7) (i : Fin 7) : Bool := i == neigh j
def edgeRow (j : Fin 7) (i : Fin 7) : Bool := single j i || i==j

theorem theta_rows : ∀ j : Fin 7, theta (single j) = false ∧ theta (edgeRow j) = true := by decide

theorem theta_needs_every_input {S k} (run : Live theta k S)
    (inputs : ∀ w, S w → w=absentBit ∨ ∃ i, w=primary i) : ∀ j, S (primary j) := by
  intro j
  apply necessary_primary run j inputs
  refine ⟨single j,edgeRow j,?_,?_⟩
  · rw [(theta_rows j).1,(theta_rows j).2]
    decide
  · intro i h
    simp [edgeRow,h]

end CoThetaFreeCore

namespace CoThetaBits
open CoThetaFreeCore

abbrev Width := 2727
abbrev Bits := BitVec Width
abbrev Wire := Bits × Bits
abbrev Row := Bool × Fin Width
def zero : Wire := (0,0)
def full : Bits := BitVec.allOnes Width
def target : Wire := (full,0)

def den (wire : Wire) (r : Row) : Bool :=
  (if r.1 then wire.1 else wire.2).getLsbD r.2.val

def gate : Kind → Wire → Wire → Wire
  | .conj,a,b => (a.1 &&& b.1,a.2 &&& b.2)
  | .disj,a,b => (a.1 ||| b.1,a.2 ||| b.2)
  | .leftOnly,a,b => (a.1 &&& ~~~b.1,a.2 &&& ~~~b.2)
  | .rightOnly,a,b => (~~~a.1 &&& b.1,~~~a.2 &&& b.2)

theorem den_injective {a b : Wire} (h : den a=den b) : a=b := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    exact congrFun h (true,⟨i,hi⟩)
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    exact congrFun h (false,⟨i,hi⟩)

theorem den_gate (kind : Kind) (a b : Wire) :
    den (gate kind a b) = fun i => applyKind kind (den a i) (den b i) := by
  funext r
  obtain ⟨side,i⟩ := r
  cases kind <;> cases side <;>
    simp [den,gate,applyKind,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,i.isLt]

theorem den_zero : den zero = absentBit := by
  funext r
  obtain ⟨s,i⟩ := r
  cases s <;> simp [den,zero,absentBit]

theorem den_target (r : Row) : den target r = r.1 := by
  obtain ⟨s,i⟩ := r
  cases s <;> simp [den,target,full,BitVec.getLsbD_allOnes,i.isLt]

def sep (w : Wire) : Bits := w.1 ^^^ w.2

def coverage : List Wire → Bits
  | [] => 0
  | w::ws => sep w ||| coverage ws

theorem bit_covered {l : List Wire} {w : Wire} (hw : w∈l) (i : Fin Width)
    (h : den w (true,i) ≠ den w (false,i)) : (coverage l).getLsbD i.val=true := by
  induction l with
  | nil => simp at hw
  | cons a xs ih =>
    rw [coverage,BitVec.getLsbD_or]
    rcases List.mem_cons.mp hw with e|mem
    · subst a
      have hd : w.1.getLsbD i.val ≠ w.2.getLsbD i.val := h
      simp only [sep,BitVec.getLsbD_xor]
      cases hp : w.1.getLsbD i.val <;> cases hn : w.2.getLsbD i.val <;> simp_all
    · simp [ih mem]

theorem live_coverage {k} {S : (Row → Bool) → Prop} (l : List Wire)
    (h : Live (den target) k S) (sub : ∀ w, S w → ∃ v∈l, den v=w) :
    coverage l = full := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let j : Fin Width := ⟨i,hi⟩
  have ne : den target (true,j) ≠ den target (false,j) := by simp [den_target]
  obtain ⟨w,hw,hd⟩ := h.separates (true,j) (false,j) ne
  obtain ⟨v,hv,eq⟩ := sub w hw
  have h1 := bit_covered hv j (eq.symm ▸ hd)
  simpa [full,BitVec.getLsbD_allOnes,hi,j] using h1

end CoThetaBits

namespace CoThetaFreeCore

theorem length_of_cover {α : Type} (xs ys : List α) (nd : xs.Nodup)
    (sub : ∀ a∈xs, a∈ys) : xs.length≤ys.length := by
  classical
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    have parts := List.nodup_cons.mp nd
    have has : a∈ys := sub a (by simp)
    have hl := erase_len a ys has
    have nextOK : xs.length≤(eraseOnce a ys).length := ih (eraseOnce a ys) parts.2 (by
      intro x hx
      have ne : x≠a := fun eq => parts.1 (eq ▸ hx)
      exact erase_preserves ne ys (sub x (List.mem_cons_of_mem _ hx)))
    simp only [List.length_cons]
    omega

end CoThetaFreeCore

namespace CoThetaBits
open CoThetaFreeCore

def Rep (ws : List Wire) (S : (Row→Bool)→Prop) : Prop :=
  ∀ f, S f ↔ ∃ w∈ws, den w=f

private theorem mem_rep {S ws} (rep : Rep ws S) (w : Wire) : w∈ws ↔ S (den w) := by
  constructor
  · intro h
    exact (rep _).2 ⟨w,h,rfl⟩
  · intro h
    obtain ⟨v,hv,e⟩ := (rep _).1 h
    exact den_injective e ▸ hv

private theorem den_nodup {ws : List Wire} (nd : ws.Nodup) : (ws.map den).Nodup := by
  induction ws with
  | nil => simp
  | cons a l ih =>
    rcases List.nodup_cons.mp nd with ⟨hne,ht⟩
    simp only [List.map_cons,List.nodup_cons]
    refine ⟨?_,ih ht⟩
    intro hm
    obtain ⟨v,hv,e⟩ := List.mem_map.mp hm
    exact hne (den_injective e ▸ hv)

theorem state_width {k S ws} (h : Live (den target) k S) (nd : ws.Nodup) (rep : Rep ws S) :
    ws.length≤k+1 := by
  obtain ⟨xs,hsize,hsub⟩ := h.width_cover
  have le := length_of_cover (ws.map den) xs (den_nodup nd) (by
    intro f hf
    obtain ⟨w,hw,eq⟩ := List.mem_map.mp hf
    exact hsub f ((rep _).2 ⟨w,hw,eq⟩))
  simpa using Nat.le_trans le hsize

def trim (a b : Wire) (ws : List Wire) : List Wire :=
  ws.filter (fun w => w != a && w != b)

theorem mem_trim {w a b : Wire} {ws : List Wire} :
    w∈trim a b ws ↔ w∈ws ∧ w≠a ∧ w≠b := by simp [trim]

def allKinds : List Kind := [.conj,.disj,.leftOnly,.rightOnly]
def options (a b : Wire) : List (List Wire) := [[],[a],[b],[a,b]]

def testStep (k : Nat) (ws : List Wire) (nextOK : List Wire → Bool) : Bool :=
  ws.any fun a => ws.any fun b => a != b &&
    (allKinds.any fun kind =>
      let z := gate kind a b
      z != zero && !(ws.contains z) &&
        (options a b).any fun keep =>
          let out := z::(keep++trim a b ws)
          out.length≤k+1 && coverage out==full && nextOK out)

def certifiedSearch : Nat → List Wire → Bool
  | 0, ws => ws.contains target
  | k+1, ws => ws.contains target || (ws.length≤k+2 && testStep k ws (certifiedSearch k))

theorem step_hit {k ws nextOK a b keep kind} (ha : a∈ws) (hb : b∈ws)
    (ab : a≠b) (hk : keep∈options a b)
    (non : gate kind a b ≠zero) (fresh : gate kind a b∉ws)
    (len : (gate kind a b::(keep++trim a b ws)).length≤k+1)
    (cov : coverage (gate kind a b::(keep++trim a b ws))=full)
    (valid : nextOK (gate kind a b::(keep++trim a b ws))=true) : testStep k ws nextOK=true := by
  have hkind : kind∈allKinds := by cases kind <;> simp [allKinds]
  unfold testStep
  apply List.any_eq_true.mpr
  refine ⟨a,ha,List.any_eq_true.mpr ⟨b,hb,?_⟩⟩
  simp only [Bool.and_eq_true,bne_iff_ne,ab,true_and,List.any_eq_true,Bool.not_eq_true']
  refine ⟨ab,kind,hkind,?_⟩
  simp [non,fresh]
  have ct : keep.length + (trim a b ws).length ≤ k := by
    simp only [List.length_cons,List.length_append] at len
    omega
  exact ⟨keep,hk,by simp [ct,cov,valid]⟩

end CoThetaBits

namespace CoThetaBits
open CoThetaFreeCore

noncomputable def kept (a b : Wire) (U : (Row→Bool)→Prop) : List Wire := by
  classical
  exact (if U (den a) then [a] else []) ++ (if U (den b) then [b] else [])

theorem is_option (a b : Wire) (U : (Row→Bool)→Prop) : kept a b U∈options a b := by
  classical
  by_cases p : U (den a) <;> by_cases q : U (den b) <;> simp [kept,options,p,q]

theorem mem_kept {v a b : Wire} {U : (Row→Bool)→Prop} :
    v∈kept a b U ↔ (v=a ∧ U (den a)) ∨ (v=b ∧ U (den b)) := by
  classical
  by_cases p : U (den a) <;> by_cases q : U (den b) <;> simp [kept,p,q]

theorem edit_member {a b v : Wire} {U : (Row→Bool)→Prop} {ws : List Wire}
    (rep : Rep ws (ins (den a) (ins (den b) U))) :
    v∈(kept a b U ++ trim a b ws) ↔ U (den v) := by
  classical
  constructor
  · intro hm
    rcases List.mem_append.mp hm with inK | inR
    · rcases mem_kept.mp inK with ⟨e,yes⟩ | ⟨e,yes⟩ <;> subst v <;> exact yes
    · obtain ⟨inside,na,nb⟩ := mem_trim.mp inR
      rcases (mem_rep rep v).1 inside with e | e | hu
      · exact (na (den_injective e)).elim
      · exact (nb (den_injective e)).elim
      · exact hu
  · intro hu
    by_cases ea : v=a
    · exact List.mem_append.mpr (Or.inl (mem_kept.mpr (Or.inl ⟨ea,ea ▸ hu⟩)))
    by_cases eb : v=b
    · exact List.mem_append.mpr (Or.inl (mem_kept.mpr (Or.inr ⟨eb,eb ▸ hu⟩)))
    apply List.mem_append.mpr
    right
    exact mem_trim.mpr ⟨(mem_rep rep v).2 (Or.inr (Or.inr hu)),ea,eb⟩

theorem edit_distinct {a b : Wire} {U : (Row→Bool)→Prop} {ws : List Wire}
    (ab : a≠b) (nd : ws.Nodup) : (kept a b U ++ trim a b ws).Nodup := by
  classical
  have ndr : (trim a b ws).Nodup := nd.filter _
  have ha : a∉trim a b ws := fun h => (mem_trim.mp h).2.1 rfl
  have hb : b∉trim a b ws := fun h => (mem_trim.mp h).2.2 rfl
  by_cases p : U (den a) <;> by_cases q : U (den b) <;>
    simp [kept,p,q,List.nodup_cons,ha,hb,ab,ndr]

theorem edit_rep {a b z : Wire} {U : (Row→Bool)→Prop} {ws : List Wire}
    (rep : Rep ws (ins (den a) (ins (den b) U))) :
    Rep (z::(kept a b U ++ trim a b ws)) (ins (den z) U) := by
  intro f
  constructor
  · intro hf
    rcases hf with e | hu
    · exact ⟨z,by simp,e.symm⟩
    · obtain ⟨v,hv,e⟩ := (rep f).1 (Or.inr (Or.inr hu))
      refine ⟨v,List.mem_cons_of_mem _ ((edit_member rep).2 ?_),e⟩
      exact e.symm ▸ hu
  · intro h
    obtain ⟨v,hv,e⟩ := h
    rcases List.mem_cons.mp hv with vz | tail
    · subst v
      exact Or.inl e.symm
    · exact Or.inr (e ▸ (edit_member rep).1 tail)

end CoThetaBits

namespace CoThetaFreeCore
variable {ρ : Type}

theorem Live.excludes_zero {goal : ρ→Bool} {k S} (h : Live goal k S)
    (ng : goal≠absentBit) : ¬S absentBit := by
  induction h with
  | stop => exact fun eq => ng eq.symm
  | step _ _ ha hb _ _ ih =>
    intro bad
    rcases bad with eq | eq | u
    · exact ha eq.symm
    · exact hb eq.symm
    · exact ih (Or.inr u)

end CoThetaFreeCore

namespace CoThetaBits
open CoThetaFreeCore

private theorem target_nonzero : den target≠absentBit := by
  intro eq
  have q := congrFun eq (true,0)
  simp [den_target,absentBit] at q

theorem certified_complete {m S} (run : Live (den target) m S) :
    ∀ fuel, m≤fuel → ∀ ws, ws.Nodup → Rep ws S → certifiedSearch fuel ws=true := by
  classical
  induction run with
  | stop =>
    intro fuel _ ws _ rep
    have ht : target∈ws := (mem_rep rep target).2 rfl
    cases fuel <;> simp [certifiedSearch,ht]
  | @step m U a b kind ab ha hb fresh tail ih =>
    intro fuel bound ws nd rep
    cases fuel with
    | zero => omega
    | succ k =>
      obtain ⟨x,hx,ex⟩ := (rep a).1 (Or.inl rfl)
      obtain ⟨y,hy,ey⟩ := (rep b).1 (Or.inr (Or.inl rfl))
      subst a
      subst b
      let z := gate kind x y
      let out := z::(kept x y U ++ trim x y ws)
      have dg : den z=(fun i => applyKind kind (den x i) (den y i)) := den_gate _ _ _
      have zab : x≠y := fun e => ab (congrArg den e)
      have nz : z≠zero := by
        intro e
        have dz : (fun i => applyKind kind (den x i) (den y i))=absentBit :=
          dg.symm.trans ((congrArg den e).trans den_zero)
        exact tail.excludes_zero target_nonzero (Or.inl dz.symm)
      have nf : z∉ws := by
        intro hz
        have st := (mem_rep rep z).1 hz
        exact fresh (dg ▸ st)
      have nextRep : Rep out (ins (fun i => applyKind kind (den x i) (den y i)) U) := by
        have e := edit_rep (z:=z) rep
        rw [dg] at e
        exact e
      have nextNd : out.Nodup := by
        apply List.nodup_cons.mpr
        refine ⟨?_,edit_distinct zab nd⟩
        intro hz
        have inU := (edit_member rep).1 hz
        exact fresh (Or.inr (Or.inr (dg ▸ inU)))
      have width := state_width tail nextNd nextRep
      have cover := live_coverage out tail (fun f hf => (nextRep f).1 hf)
      have verdict := ih k (by omega) out nextNd nextRep
      have stepOk : testStep k ws (certifiedSearch k)=true :=
        step_hit hx hy zab (is_option x y U) nz nf (Nat.le_trans width (by omega)) cover verdict
      have current := Live.step kind ab ha hb fresh tail
      have max := state_width current nd rep
      have size : ws.length≤k+2 := by omega
      simp [certifiedSearch,size,stepOk]

end CoThetaBits

namespace CoThetaBits
open CoThetaFreeCore

def raw : List Wire := [
  (0x7ffffff0000001ffffffc0000007ffffff0000001ffffffc0000007ffffff0000001ffffffc0000007ffffff0000001ffffffc0000007ffffff0000001ffffffc0000007ffffff0000001ffffffc0000007ffffff0000001ffffffc0000007ffffff0000001ffffffc0000007ffffff0000001ffffffc0000007ffffff0000001ffffffc0000007ffffff0000001fffffffffffff8000000ffffffe0000003fffffffffffff0000001fffffffffffff8000000fffffffffffffc0000007ffffff0000001ffffffc0000007ffffff0000001ffffffc0000007ffffff0000001fffffffffffff8000000fffffffffffffc0000007ffffffffffffffffffffffffff8000000fffffffffffffffffffffffffff0000001ffffffc0000007ffffff0000001ffffffc0000007ffffff0000001fffffffffffff8000000ffffffe0000003ffffffffffffffffffffffffffc0000007ffffff,0x210020a42004148400829080105210020a42004148400829080105210020a42004148400829080105210020a42004148400829080105210020a42004148400829080105210020a42004148400829080105210020a42004148400829080105210020a42004148400829080105210020a42004148400829080105210020a42004148400829080105210020a42004148400829080105210020a42004148400829080105210020a42004148400829080105210020a42004148400829080105210020a42004148400829080105210020a42004148400829080105210020a42004148400829080105210020a42004148400829080105210020a42004148400829080105210020a42004148400829080105210020a42004148400829080105210020a42004148400829080105210020a42004148400829080105210020a42004148400829080105210020a42004148400829080105210020a),
  (0x7ffffffffffffe00000000000007ffffffffffffe00000000000007ffffffffffffe00000000000007ffffffffffffe00000000000007ffffffffffffe00000000000007ffffffffffffe00000000000007ffffffffffffe00000000000007ffffffffffffe00000000000007ffffffffffffe00000000000007ffffffffffffe00000000000007ffffffffffffe0000003ffffffffffffffffffffffffffc0000007ffffffffffffe0000003fffffffffffff0000001ffffffffffffffffffffffffffe00000000000007ffffffffffffe00000000000007ffffffffffffe0000003fffffffffffff0000001fffffffffffff8000000ffffffe0000003fffffffffffff0000001ffffffc0000007ffffffffffffe00000000000007ffffffffffffe00000000000007ffffffffffffe0000003ffffffffffffffffffffffffffc0000007ffffff0000001fffffffffffff8000000,0x904c00120980024130004826000904c00120980024130004826000904c00120980024130004826000904c00120980024130004826000904c00120980024130004826000904c00120980024130004826000904c00120980024130004826000904c00120980024130004826000904c00120980024130004826000904c00120980024130004826000904c00120980024130004826000904c00120980024130004826000904c00120980024130004826000904c00120980024130004826000904c00120980024130004826000904c00120980024130004826000904c00120980024130004826000904c00120980024130004826000904c00120980024130004826000904c00120980024130004826000904c00120980024130004826000904c00120980024130004826000904c00120980024130004826000904c00120980024130004826000904c00120980024130004826000904c),
  (0x7ffffffffffffffffffffffffff8000000000000000000000000007ffffffffffffffffffffffffff8000000000000000000000000007ffffffffffffffffffffffffff8000000000000000000000000007ffffffffffffffffffffffffff8000000000000000000000000007ffffffffffffffffffffffffff8000000000000000000000000007fffffffffffffffffffc0000000000000ffffffffffffffffffff800000000000000000003fffffffffffffffffffe00000000000007ffffffffffffffffffffffffff8000000000000000000000000007fffffffffffffffffffc00000000000000000001ffffffffffffffffffff00000000000003fffffffffffffffffffe00000000000007ffffffffffffffffffffffffff8000000000000000000000000007fffffffffffffffffffc0000000000000ffffffffffffffffffff80000000000001ffffffffffffffffffff,0x4a5249094a492129492425292484a5249094a492129492425292484a5249094a492129492425292484a5249094a492129492425292484a5249094a492129492425292484a5249094a492129492425292484a5249094a492129492425292484a5249094a492129492425292484a5249094a492129492425292484a5249094a492129492425292484a5249094a492129492425292484a5249094a492129492425292484a5249094a492129492425292484a5249094a492129492425292484a5249094a492129492425292484a5249094a492129492425292484a5249094a492129492425292484a5249094a492129492425292484a5249094a492129492425292484a5249094a492129492425292484a5249094a492129492425292484a5249094a492129492425292484a5249094a492129492425292484a5249094a492129492425292484a5249094a492129492425292484a52490),
  (0x7fffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffffffffffffffff80000000000000000000000000000000000000001fffffffffffffffffffffffffffffffffc0000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000fffffffffffffffffffffffffffffffffe00000000000000000000,0xc1c0e018381c0307038060e0700c1c0e018381c0307038060e0700c1c0e018381c0307038060e0700c1c0e018381c0307038060e0700c1c0e018381c0307038060e0700c1c0e018381c0307038060e0700c1c0e018381c0307038060e0700c1c0e018381c0307038060e0700c1c0e018381c0307038060e0700c1c0e018381c0307038060e0700c1c0e018381c0307038060e0700c1c0e018381c0307038060e0700c1c0e018381c0307038060e0700c1c0e018381c0307038060e0700c1c0e018381c0307038060e0700c1c0e018381c0307038060e0700c1c0e018381c0307038060e0700c1c0e018381c0307038060e0700c1c0e018381c0307038060e0700c1c0e018381c0307038060e0700c1c0e018381c0307038060e0700c1c0e018381c0307038060e0700c1c0e018381c0307038060e0700c1c0e018381c0307038060e0700c1c0e018381c0307038060e0700c1c0e0),
  (0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000000000000000000000000000000000000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000,0x7060700e0c0e01c181c038303807060700e0c0e01c181c038303807060700e0c0e01c181c038303807060700e0c0e01c181c038303807060700e0c0e01c181c038303807060700e0c0e01c181c038303807060700e0c0e01c181c038303807060700e0c0e01c181c038303807060700e0c0e01c181c038303807060700e0c0e01c181c038303807060700e0c0e01c181c038303807060700e0c0e01c181c038303807060700e0c0e01c181c038303807060700e0c0e01c181c038303807060700e0c0e01c181c038303807060700e0c0e01c181c038303807060700e0c0e01c181c038303807060700e0c0e01c181c038303807060700e0c0e01c181c038303807060700e0c0e01c181c038303807060700e0c0e01c181c038303807060700e0c0e01c181c038303807060700e0c0e01c181c038303807060700e0c0e01c181c038303807060700e0c0e01c181c038303807060700),
  (0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x7f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f800),
  (0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x7f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000ff00001fe00003fc00007f80000)]

def col (j : Fin 7) : Wire := raw[j.val]?.getD zero
def sample (r : Row) (j : Fin 7) : Bool := den (col j) r
def empty : Row := (false,0)
def start : List (Row→Bool) := (fun _ => false)::(fun _ => true)::raw.map den

def edgeWord : Wire := (gate .disj (gate .disj (gate .disj (gate .disj (gate .disj (gate .disj (gate .disj (gate .conj (col 0) (col 2)) (gate .conj (col 1) (col 2))) (gate .conj (col 0) (col 3))) (gate .conj (col 3) (col 4))) (gate .conj (col 1) (col 4))) (gate .conj (col 0) (col 5))) (gate .conj (col 5) (col 6))) (gate .conj (col 1) (col 6)))

theorem edge_exact : edgeWord=target := by decide +kernel
theorem sample_correct (r : Row) : CoThetaFreeCore.theta (sample r)=den target r := by
  have h := congrFun (congrArg den edge_exact) r
  simp only [edgeWord,den_gate,applyKind] at h
  exact h

theorem raw_is_ofFn : List.ofFn col=raw := rfl
theorem raw_nodup : raw.Nodup := by decide +kernel
theorem low_raw : ∀ j : Fin 7, den (col j) empty=false := by decide +kernel

def privateIndex (j : Fin 7) : Fin Width := match j.val with
  | 0 => 4
  | 1 => 31
  | 2 => 1
  | 3 => 82
  | 4 => 218
  | 5 => 568
  | _ => 1217

theorem private_row : ∀ j k : Fin 7,
    den (col k) (true,privateIndex j) ≠ den (col k) (false,privateIndex j) → k=j := by decide +kernel

private theorem indexed {v : Wire} (h : v∈raw) : ∃ j, col j=v := by
  rw [←raw_is_ofFn] at h
  exact List.mem_ofFn.mp h

theorem root_rep {k S} (h : Live (den target) k S)
    (inputs : ∀ f, S f → f=absentBit ∨ ∃ j, den (col j)=f) : Rep raw S := by
  have allcol (j : Fin 7) : S (den (col j)) := by
    let i := privateIndex j
    have diff : den target (true,i) ≠ den target (false,i) := by simp [den_target]
    obtain ⟨v,hv,hd⟩ := h.separates (true,i) (false,i) diff
    rcases inputs v hv with z | ⟨l,e⟩
    · subst v
      exact (hd rfl).elim
    · subst v
      obtain rfl := private_row j l hd
      exact hv
  intro f
  constructor
  · intro hf
    rcases inputs f hf with z | ⟨j,eq⟩
    · exact (h.excludes_zero target_nonzero (z ▸ hf)).elim
    · refine ⟨col j,?_,eq⟩
      rw [←raw_is_ofFn]
      exact List.mem_ofFn.mpr ⟨j,rfl⟩
  · rintro ⟨v,hv,eq⟩
    obtain ⟨j,rfl⟩ := indexed hv
    exact eq ▸ allcol j

theorem root_input {f : Row→Bool} (hm : f∈start.map (norm empty)) :
    f=absentBit ∨ ∃ j, den (col j)=f := by
  obtain ⟨v,hin,rfl⟩ := List.mem_map.mp hm
  rcases List.mem_cons.mp hin with e | tail
  · subst v
    exact Or.inl rfl
  rcases List.mem_cons.mp tail with e | t
  · subst v
    exact Or.inl rfl
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp t
  obtain ⟨j,rfl⟩ := indexed hw
  right
  refine ⟨j,?_⟩
  funext r
  simp [norm,low_raw j,phase]

theorem no_small_ordinary (certificate : certifiedSearch 10 raw=false)
    {n ws} (program : Ordinary start n ws) (cost : n≤10) (out : den target∈ws) : False := by
  obtain ⟨ys,fre,contains⟩ := simulate_all_wires empty program
  have self : norm empty (den target)=den target := by
    funext r
    simp [norm,den_target,empty,phase]
  have hin : den target∈ys := self ▸ contains _ out
  have rn : absentBit∈start.map (norm empty) := by
    change absentBit∈(absentBit::_)
    simp
  obtain ⟨m,S,le,live,sub⟩ :=
    rewind fre rn (Live.stop (goal:=den target)) (fun w eq => eq.symm ▸ hin)
  have rep := root_rep live (fun f hf => root_input (sub f hf))
  have yes := certified_complete live 10 (by omega) raw raw_nodup rep
  exact Bool.false_ne_true (certificate.symm.trans yes)

end CoThetaBits

namespace CoThetaFreeCore

variable {ρ : Type}

inductive PinForm where
  | constant (v : Bool)
  | copy (i : Nat)
  | inv (i : Nat)
  | binary (join : Bool) (i j : Nat)

def PinForm.value : PinForm → List (ρ→Bool) → (ρ→Bool)
  | .constant v, _ => fun _ => v
  | .copy i, w => w.getD i absentBit
  | .inv i, w => fun r => !(w.getD i absentBit r)
  | .binary join i j, w => fun r => base join (w.getD i absentBit r) (w.getD j absentBit r)

def PinForm.binaryCost : PinForm → Nat
  | .binary _ _ _ => 1
  | _ => 0

def cost : List PinForm → Nat
  | [] => 0
  | f::fs => f.binaryCost + cost fs

def execute : List PinForm → List (ρ→Bool) → List (ρ→Bool)
  | [], w => w
  | f::fs, w => execute fs (w ++ [f.value w])

private theorem read_registered (w pool : List (ρ→Bool)) (i : Nat) (hz : absentBit∈pool)
    (known : ∀ v∈w, v∈pool) : w.getD i absentBit∈pool := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact hz
  | some a => exact known a (List.mem_of_getElem? h)

private theorem pin_step (f : PinForm) (w pool raw : List (ρ→Bool)) (n : Nat)
    (pre : Ordinary raw n pool) (consts : ∀ b : Bool, (fun _ : ρ => b) ∈ pool)
    (known : ∀ v∈w, v∈pool) :
    ∃ ys, Ordinary raw (n+f.binaryCost) ys ∧
      (∀ v∈pool, v∈ys) ∧ f.value w∈ys := by
  have reg := read_registered w pool
  have hz : absentBit∈pool := consts false
  cases f with
  | constant v => exact ⟨pool,pre,fun _ h => h,consts _⟩
  | copy i => exact ⟨pool,pre,fun _ h => h,reg i hz known⟩
  | inv i =>
    exact ⟨_, Ordinary.inv pre (reg i hz known),
      fun _ h => List.mem_cons_of_mem _ h,by simp [PinForm.value]⟩
  | binary join i j =>
    exact ⟨_, Ordinary.binary pre join (reg i hz known) (reg j hz known),
      fun _ h => List.mem_cons_of_mem _ h,by simp [PinForm.value]⟩

theorem pins_to_program (fs : List PinForm) (w pool raw : List (ρ→Bool)) (n : Nat)
    (pre : Ordinary raw n pool) (consts : ∀ b : Bool, (fun _ : ρ => b) ∈ pool)
    (known : ∀ v∈w, v∈pool) :
    ∃ ys, Ordinary raw (n+cost fs) ys ∧ ∀ v∈execute fs w, v∈ys := by
  induction fs generalizing w pool n with
  | nil => exact ⟨_,pre,known⟩
  | cons f fs ih =>
    obtain ⟨mid,hmid,old,hw⟩ := pin_step f w pool raw n pre consts known
    have available (v) (h : v∈w++[f.value w]) : v∈mid := by
      rcases List.mem_append.mp h with original | fresh
      · exact old _ (known _ original)
      · exact (congrArg (fun u => u∈mid) (List.mem_singleton.mp fresh)).mpr hw
    obtain ⟨ys,hy,sub⟩ := ih (w++[f.value w]) mid (n+f.binaryCost) hmid
      (fun b => old _ (consts b)) available
    exact ⟨ys,by simpa [cost,Nat.add_assoc] using hy,sub⟩

end CoThetaFreeCore

namespace CoThetaPhysical
open CoThetaFreeCore PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gateForm (g : Gate) : PinForm :=
  match g.op, g.inputs with
  | .and, [] => .constant true
  | .or, [] => .constant false
  | .not, [] => .constant true
  | .and, [i] | .or, [i] => .copy i
  | .not, i::_ => .inv i
  | .and, i::j::_ => .binary false i j
  | .or, i::j::_ => .binary true i j
  | _, _ => .constant false

def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length≤2

private theorem read_word {ρ : Type} (w : List (ρ→Bool)) (i : Nat) (r : ρ) :
    ((w.map (fun f => f r)).getD i false) = w.getD i absentBit r := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[i]? <;> rfl

private theorem read_option {ρ : Type} (o : Option (ρ→Bool)) (r : ρ) :
    (o.map (fun f => f r)).getD false = o.getD absentBit r := by cases o <;> rfl

theorem form_agrees {ρ : Type} (g : Gate) (hg : legal g) (w : List (ρ→Bool)) (r : ρ) :
    (gateForm g).value w r =
    g.op.eval (g.inputs.map fun i => (w.map (fun f => f r)).getD i false) := by
  obtain ⟨op,pins⟩ := g
  obtain ⟨hop,hlen⟩ := hg
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
  change op=GateOp.and ∨ op=GateOp.or ∨ op=GateOp.not at hop
  change pins.length≤2 at hlen
  rcases hop with rfl | rfl | rfl <;>
    cases pins with
    | nil => rfl
    | cons i xs =>
      cases xs with
      | nil => simp [gateForm,PinForm.value,GateOp.eval,base,read_word,read_option]
      | cons j t =>
        cases t with
        | nil => simp [gateForm,PinForm.value,GateOp.eval,base,read_word,read_option]
        | cons h t => simp at hlen

theorem map_execute {ρ : Type} (gs : List Gate) (w : List (ρ→Bool)) (r : ρ)
    (hg : ∀ g∈gs, legal g) :
    (execute (gs.map gateForm) w).map (fun f => f r) =
    gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)])
      (w.map (fun f => f r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons,execute,List.foldl_cons]
    rw [ih _ (fun a ha => hg a (List.mem_cons_of_mem _ ha))]
    simp [form_agrees g (hg _ (by simp)) w r]

theorem circuit_rows {ρ : Type} (C : Circuit) (hf : FanInTwo C) (w : List (ρ→Bool)) (r : ρ) :
    (execute (C.gates.map gateForm) w).map (fun f => f r) = C.wires (w.map (fun f => f r)) :=
  map_execute C.gates w r hf

def boolCost (g : Gate) : Nat :=
  match g.op with
  | .and | .or => 1
  | _ => 0

theorem form_cost_le (g : Gate) : (gateForm g).binaryCost ≤ boolCost g := by
  obtain ⟨op,pins⟩ := g
  cases op <;> cases pins with
    | nil => simp [gateForm,boolCost,PinForm.binaryCost]
    | cons i t => cases t <;> simp [gateForm,boolCost,PinForm.binaryCost]

theorem cost_le_binary (gs : List Gate) :
    cost (gs.map gateForm) ≤ (gs.map boolCost).sum := by
  induction gs with
  | nil => simp [cost]
  | cons g gs ih =>
    simp only [List.map_cons,cost,List.sum_cons]
    exact Nat.add_le_add (form_cost_le g) ih

end CoThetaPhysical

namespace CoThetaOfficial
open CoThetaFreeCore CoThetaBits CoThetaPhysical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private theorem evaluated_input (r : Row) :
    (CoThetaBits.raw.map den).map (fun f => f r) = List.ofFn (sample r) := by
  rw [←raw_is_ofFn]
  rw [List.map_ofFn,List.map_ofFn]
  rfl

private theorem word_read {ρ : Type} (w : List (ρ→Bool)) (i : Nat) (r : ρ) :
    (w.map (fun f => f r)).getD i false = w.getD i absentBit r := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[i]? <;> rfl

theorem physical_theta_lower (certificate : certifiedSearch 10 CoThetaBits.raw=false)
    (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x)=CoThetaFreeCore.theta x) :
    11 ≤ (C.gates.map boolCost).sum := by
  by_contra! small
  let w := CoThetaBits.raw.map den
  let fs := C.gates.map gateForm
  let result := (execute fs w).getD C.output absentBit
  have eq : result=den target := by
    funext r
    have hw := congrArg (fun q : List Bool => q.getD C.output false) (circuit_rows C fan w r)
    change ((execute fs w).map (fun f => f r)).getD C.output false =
      (C.wires (w.map (fun f => f r))).getD C.output false at hw
    rw [word_read] at hw
    have hr := correct (sample r)
    rw [←evaluated_input] at hr
    exact hw.trans (hr.trans (sample_correct r))
  have present : result∈execute fs w := by
    cases h : (execute fs w)[C.output]? with
    | none =>
      have bad : result=absentBit := by simp [result,List.getD_eq_getElem?_getD,h]
      have hm := congrFun (eq.symm.trans bad) (true,0)
      simp [den_target,absentBit] at hm
    | some v =>
      have hv : result=v := by simp [result,List.getD_eq_getElem?_getD,h]
      exact hv.symm ▸ List.mem_of_getElem? h
  have constants (b : Bool) : (fun _ : Row => b)∈CoThetaBits.start := by
    cases b <;> simp [CoThetaBits.start]
  have already (v) (hv : v∈w) : v∈CoThetaBits.start :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv)
  obtain ⟨ys,program,cover⟩ := pins_to_program fs w CoThetaBits.start CoThetaBits.start 0
    Ordinary.start constants already
  have b := cost_le_binary C.gates
  exact no_small_ordinary certificate program (by dsimp [fs]; omega) (eq ▸ cover _ present)

end CoThetaOfficial
