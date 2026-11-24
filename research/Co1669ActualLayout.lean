import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1669
-- Ordinary edge-head theorem reproduced from the checked proof by loris-olsem.
namespace Prior1667
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

inductive Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | stop (hp : proper target) : Live target 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
      Live target (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
      Live target (k+1) t (insert a (insert b U))

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩


def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]




abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a

inductive Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | start : Reach roots 0 roots
  | one {p bank a} : Reach roots p bank → Available bank a →
      Reach roots (p+1) (inv a :: bank)
  | two {p bank a b} (op : Bool) : Reach roots p bank → Available bank a →
      Available bank b → Reach roots (p+1) (combine op a b :: bank)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

inductive Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | stop : Run goal 0 [goal]
  | perm {s xs zs} : xs.Perm zs → Run goal s xs → Run goal s zs
  | one {s a rest} (save : Bool) : Run goal s (inv a :: kept save a rest) →
      Run goal (s+1) (a::rest)
  | two {s a b rest} (op ka kb : Bool) :
      Run goal s (combine op a b :: kept ka a (kept kb b rest)) →
      Run goal (s+1) (a::b::rest)

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩

theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v := by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr

theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next, Reach roots q next ∧ Available next (inv a) ∧
        (∀ v, Available bank v → Available next v) ∧ q+cost a ≤ p+1+cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩

theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
        (∀ v, Available bank v → Available next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r
  cases d <;> exact bit_bin _ _ _ _

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g) = bin d (table f) (table g) := by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]

theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a) := by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false) = zero := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true) = one := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z

theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witness w z) (hs : ∀ a ∈ S, a ∈ z::w) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm

theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l v U, l ≤ p+k ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ha ih =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩

theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S, k ≤ p ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs

theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def seed : Sig := 0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 && sample r 1) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed_nonzero : seed ≠ zero := by decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

theorem exec_extends (gs : List Gate) (ws : List Sig) : ∃ l, execute gs ws = ws ++ l := by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩ := ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩

def neighbor (i : Fin 9) : Nat := [4,2,1,2,3,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))

theorem seed_witness : ∀ i : Fin 9,
    (bit (absentRow i) graph != bit (presentRow i) graph) &&
    ((inputs++[seed]).all fun w => w == inputs.getD i.val zero ||
      bit (absentRow i) w == bit (presentRow i) w) = true := by decide +kernel

theorem all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[seed]) :
    S=inputs.toFinset ∨ S=(inputs++[seed]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := seed_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (absentRow i) (presentRow i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : seed ∈ S
  · right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [List.mem_append,List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hseed)
  · left
    exact Finset.Subset.antisymm (fun w hw => by
      have hx := sub w hw
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hin | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hseed hw)) needed

def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → ¬Live T k t S
theorem zero_suffix (deadCase : Impossible graph 14 inputs.toFinset)
    (D : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo D)
    (computes : ∀ x, D.eval (List.ofFn x ++ [false]) = edge x) : 15 ≤ D.size := by
  by_contra! small
  have goalEq : (execute D.gates (inputs++[zero])).getD D.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r ((execute D.gates (inputs++[zero])).getD D.output zero) = bit r graph
    rw [←b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1),List.map_append,←sampled]
    simp only [List.map_cons,List.map_nil,bit_zero]
    exact (computes (sample r)).trans (edge_table r).symm
  have out := get_rep (execute D.gates (inputs++[zero])) D.output
  rw [goalEq] at out
  have mem := out.resolve_right (fun hn => hn graph_proper)
  obtain ⟨k,t,S,hk,run,hs⟩ := extract D.gates _ legal graph_proper mem
  have raw (w : Sig) (hw : w∈S) : w∈inputs := by
    rcases List.mem_append.mp (hs w hw) with h|h
    · exact h
    · have eq := List.mem_singleton.mp h
      exact ((live_proper run w hw).1 eq).elim
  have eq : S = inputs.toFinset := by
    rcases all_roots run (fun a ha => List.mem_append_left _ (raw a ha)) with h|h
    · exact h
    · have se : seed∈S := by rw [h]; simp
      have notmem : seed∉inputs := by decide +kernel
      exact (notmem (raw _ se)).elim
  have len : D.gates.length<15 := small
  exact deadCase k t (by omega) (eq ▸ run)

end Prior1667
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

namespace CoThetaFreeCore

structure TraceGate (ρ : Type) where
  kind : Kind
  left : ρ → Bool
  right : ρ → Bool

def TraceGate.value {ρ} (g : TraceGate ρ) : ρ → Bool :=
  fun r => applyKind g.kind (g.left r) (g.right r)

def registered {ρ} (raw : List (ρ→Bool)) : List (TraceGate ρ) → Prop
  | [] => True
  | g::gs => g.left∈raw ∧ g.right∈raw ∧ registered (g.value::raw) gs

def traceWires {ρ} (raw : List (ρ→Bool)) : List (TraceGate ρ) → List (ρ→Bool)
  | [] => raw
  | g::gs => traceWires (g.value::raw) gs

def restrict {ρ σ} (lift : σ→ρ) (wire : ρ→Bool) : σ→Bool := fun i => wire (lift i)

def disappears {ρ σ} (lift : σ→ρ) (g : TraceGate ρ) : Prop :=
  restrict lift g.left=absentBit ∨ restrict lift g.right=absentBit

noncomputable def remaining {ρ σ} (lift : σ→ρ) : List (TraceGate ρ) → Nat
  | [] => 0
  | g::gs => by
    classical
    exact (if disappears lift g then 0 else 1) + remaining lift gs

noncomputable def saved {ρ σ} (lift : σ→ρ) : List (TraceGate ρ) → Nat
  | [] => 0
  | g::gs => by
    classical
    exact (if disappears lift g then 1 else 0) + saved lift gs

theorem accounted {ρ σ} (lift : σ→ρ) (gs : List (TraceGate ρ)) :
    remaining lift gs + saved lift gs = gs.length := by
  classical
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    by_cases h : disappears lift g <;> simp [remaining,saved,h] <;> omega

private theorem trace_step {ρ σ} (lift : σ→ρ) (g : TraceGate ρ)
    {init pool : List (σ→Bool)} {n} (live : Free init n pool)
    (ha : restrict lift g.left∈pool) (hb : restrict lift g.right∈pool)
    (hz : absentBit∈pool) :
    ∃ k ys, (disappears lift g → k=0) ∧ (¬disappears lift g → k=1) ∧
      Free init (n+k) ys ∧ (∀ a∈pool,a∈ys) ∧ restrict lift g.value∈ys := by
  classical
  by_cases drop : disappears lift g
  · refine ⟨0,pool,fun _ => rfl,fun n => (n drop).elim,live,fun _ h => h,?_⟩
    change (fun r => applyKind g.kind (restrict lift g.left r) (restrict lift g.right r))∈pool
    rcases drop with lo|lo
    · rw [lo]
      rcases zero_left g.kind (restrict lift g.right) with e|e
      · exact (congrArg (fun v => v∈pool) e).mpr hb
      · exact (congrArg (fun v => v∈pool) e).mpr hz
    · rw [lo]
      rcases zero_right g.kind (restrict lift g.left) with e|e
      · exact (congrArg (fun v => v∈pool) e).mpr ha
      · exact (congrArg (fun v => v∈pool) e).mpr hz
  · exact ⟨1,_,fun h => (drop h).elim,fun _ => rfl,Free.binary live g.kind ha hb,
      fun _ h => List.mem_cons_of_mem _ h,List.mem_cons_self⟩

theorem restrict_trace {ρ σ} (lift : σ→ρ) (gs : List (TraceGate ρ))
    {start : List (ρ→Bool)} {init pool : List (σ→Bool)} {n}
    (good : registered start gs) (pre : Free init n pool) (hz : absentBit∈pool)
    (known : ∀ w∈start,restrict lift w∈pool) :
    ∃ ys, Free init (n+remaining lift gs) ys ∧ ∀ w∈traceWires start gs,restrict lift w∈ys := by
  classical
  induction gs generalizing start pool n with
  | nil => exact ⟨_,pre,known⟩
  | cons g gs ih =>
    rcases good with ⟨left,right,rest⟩
    obtain ⟨k,mid,zeroCost,oneCost,step,old,output⟩ :=
      trace_step lift g pre (known _ left) (known _ right) hz
    have fresh (w) (h : w∈g.value::start) : restrict lift w∈mid := by
      rcases List.mem_cons.mp h with e|h
      · exact (congrArg (fun v => restrict lift v∈mid) e).mpr output
      · exact old _ (known _ h)
    obtain ⟨ys,tail,available⟩ := ih rest step (old _ hz) fresh
    refine ⟨ys,?_,available⟩
    by_cases d : disappears lift g
    · have eq := zeroCost d
      simpa [remaining,d,eq] using tail
    · have eq := oneCost d
      simpa [remaining,d,eq,Nat.add_assoc] using tail

end CoThetaFreeCore

namespace CoThetaFreeCore

theorem trace_append {ρ} (raw : List (ρ→Bool)) (a b : List (TraceGate ρ)) :
    traceWires raw (a++b)=traceWires (traceWires raw a) b := by
  induction a generalizing raw with
  | nil => rfl
  | cons x xs ih => exact ih (x.value::raw)

theorem registered_append {ρ} (raw : List (ρ→Bool)) (a b : List (TraceGate ρ)) :
    registered raw (a++b) ↔ registered raw a ∧ registered (traceWires raw a) b := by
  induction a generalizing raw with
  | nil => simp [registered,traceWires]
  | cons x xs ih =>
    simp only [List.cons_append,registered,traceWires,ih]
    simp [and_assoc]

theorem trace_of_free {ρ} {raw ws : List (ρ→Bool)} {n} (p : Free raw n ws) :
    ∃ gs : List (TraceGate ρ), gs.length=n ∧ registered raw gs ∧ traceWires raw gs=ws := by
  induction p with
  | start => exact ⟨[],rfl,True.intro,rfl⟩
  | @binary n ws a b pre kind ha hb ih =>
    obtain ⟨s,len,reg,eq⟩ := ih
    let g : TraceGate ρ := ⟨kind,a,b⟩
    refine ⟨s++[g],by simp [len],(registered_append _ _ _).2 ⟨reg,?_⟩,?_⟩
    · simpa [eq,registered,g] using And.intro ha hb
    · rw [trace_append,eq]
      rfl

def reads {ρ} (g : TraceGate ρ) (wire : ρ→Bool) : Prop := g.left=wire ∨ g.right=wire

theorem reading_zero_disappears {ρ σ} (lift : σ→ρ) {g : TraceGate ρ} {wire}
    (drop : restrict lift wire=absentBit) (h : reads g wire) : disappears lift g := by
  rcases h with e|e
  · exact Or.inl ((congrArg (restrict lift) e).trans drop)
  · exact Or.inr ((congrArg (restrict lift) e).trans drop)

theorem two_zero_propagate {ρ σ} (lift : σ→ρ) (g : TraceGate ρ)
    (l : restrict lift g.left=absentBit) (r : restrict lift g.right=absentBit) :
    restrict lift g.value=absentBit := by
  funext i
  change applyKind g.kind (restrict lift g.left i) (restrict lift g.right i) = false
  rw [l,r]
  cases g.kind <;> rfl

end CoThetaFreeCore
namespace CoThetaFreeCore

def agreeOutside {ρ : Type} (E : (ρ → Bool) → Prop) (r s : ρ)
    (ws : List (ρ → Bool)) : Prop := ∀ w∈ws, ¬ E w → w r = w s

theorem trace_barrier {ρ : Type} (E : (ρ→Bool)→Prop) (r s : ρ)
    (gs : List (TraceGate ρ)) {raw} (well : registered raw gs)
    (sources : agreeOutside E r s raw)
    (blocked : ∀ g∈gs, (E g.left ∨ E g.right) → g.value r=g.value s) :
    agreeOutside E r s (traceWires raw gs) := by
  classical
  induction gs generalizing raw with
  | nil => exact sources
  | cons g gs ih =>
    rcases well with ⟨hl,hr,rest⟩
    have same : g.value r=g.value s := by
      by_cases h : E g.left ∨ E g.right
      · exact blocked g (by simp) h
      · have le := sources g.left hl (fun x => h (Or.inl x))
        have re := sources g.right hr (fun x => h (Or.inr x))
        simp only [TraceGate.value,le,re]
    apply ih rest _ (fun t ht => blocked t (List.mem_cons_of_mem _ ht))
    intro w hw n
    rcases List.mem_cons.mp hw with e|h
    · exact e ▸ same
    · exact sources w h n

theorem reader_witness {ρ : Type} (E : (ρ→Bool)→Prop) (r s : ρ)
    {gs : List (TraceGate ρ)} {raw out} (well : registered raw gs)
    (sources : agreeOutside E r s raw) (hOut : out∈traceWires raw gs)
    (clear : ¬ E out) (diff : out r ≠ out s) :
    ∃ g∈gs, (E g.left ∨ E g.right) ∧ g.value r≠g.value s := by
  classical
  apply Classical.byContradiction
  intro bad
  apply diff
  apply trace_barrier E r s gs well sources _ out hOut clear
  intro g hg he
  apply Classical.byContradiction
  intro ne
  exact bad ⟨g,hg,he,ne⟩

theorem second_reader {ρ : Type} (x : ρ→Bool) (r s : ρ)
    {gs : List (TraceGate ρ)} {raw out} (gate : TraceGate ρ)
    (well : registered raw gs) (source : agreeOutside (·=x) r s raw)
    (hOut : out∈traceWires raw gs) (distinct : out≠x) (diff : out r ≠ out s)
    (masked : gate.value r=gate.value s) :
    ∃ g∈gs, reads g x ∧ g≠gate := by
  obtain ⟨g,hg,reader,ne⟩ := reader_witness (·=x) r s well source hOut distinct diff
  exact ⟨g,hg,reader,fun e => ne (e ▸ masked)⟩

end CoThetaFreeCore
namespace CoThetaFreeCore

def sufficient {ρ : Type} (raw : List (ρ→Bool)) (out : ρ→Bool)
    (gs : List (TraceGate ρ)) : Prop := registered raw gs ∧ out∈traceWires raw gs

def freshTrace {ρ : Type} (raw : List (ρ→Bool)) : List (TraceGate ρ)→Prop
  | [] => True
  | g::gs => g.value∉raw ∧ freshTrace (g.value::raw) gs

theorem trace_subset {ρ : Type} (gs : List (TraceGate ρ)) {as bs}
    (sub : ∀ w∈as,w∈bs) :
    (registered as gs → registered bs gs) ∧
      ∀ w∈traceWires as gs,w∈traceWires bs gs := by
  induction gs generalizing as bs with
  | nil => exact ⟨fun _ => True.intro,sub⟩
  | cons g tail ih =>
    have next : ∀ w∈g.value::as,w∈g.value::bs := by
      intro w hw
      rcases List.mem_cons.mp hw with e|h
      · exact List.mem_cons.mpr (Or.inl e)
      · exact List.mem_cons_of_mem _ (sub _ h)
    have h := ih next
    exact ⟨fun ok => ⟨sub _ ok.1,sub _ ok.2.1,h.1 ok.2.2⟩,h.2⟩

theorem simplify_trace {ρ : Type} {raw : List (ρ→Bool)} {out : ρ→Bool}
    (gs : List (TraceGate ρ)) (solves : sufficient raw out gs) :
    ∃ ts : List (TraceGate ρ), sufficient raw out ts ∧ freshTrace raw ts ∧
      (ts.length≤gs.length ∧ (¬freshTrace raw gs → ts.length<gs.length)) := by
  classical
  induction gs generalizing raw with
  | nil => exact ⟨[],solves,True.intro,Nat.le_refl _,fun bad => (bad True.intro).elim⟩
  | cons g gs ih =>
    obtain ⟨reg,output⟩ := solves
    rcases reg with ⟨left,right,rest⟩
    by_cases seen : g.value∈raw
    · have cover : ∀ w∈g.value::raw,w∈raw := by
        intro w h
        rcases List.mem_cons.mp h with e|h
        · exact e ▸ seen
        · exact h
      have reduce := trace_subset gs cover
      obtain ⟨ts,ok,fresh,le,_⟩ := ih ⟨reduce.1 rest,reduce.2 out output⟩
      refine ⟨ts,ok,fresh,?_,?_⟩ <;> simp only [List.length_cons] <;> omega
    · obtain ⟨ts,ok,fresh,le,lt⟩ := ih ⟨rest,output⟩
      refine ⟨g::ts,⟨⟨left,right,ok.1⟩,ok.2⟩,⟨seen,fresh⟩,?_,?_⟩
      · simp only [List.length_cons]
        omega
      · intro bad
        have h := lt (fun f => bad (And.intro seen f))
        simp only [List.length_cons]
        omega

theorem trace_minimal_fresh {ρ : Type} {raw : List (ρ→Bool)} {out : ρ→Bool}
    {gs : List (TraceGate ρ)} (solves : sufficient raw out gs)
    (minimal : ∀ ts, sufficient raw out ts → gs.length≤ts.length) : freshTrace raw gs := by
  classical
  apply Classical.byContradiction
  intro bad
  obtain ⟨ts,h,_,_,lt⟩ := simplify_trace gs solves
  have small := lt bad
  have big := minimal ts h
  omega

theorem fresh_outputs {ρ : Type} {raw : List (ρ→Bool)} {gs : List (TraceGate ρ)}
    (fresh : freshTrace raw gs) (g : TraceGate ρ) (hg : g∈gs) : g.value∉raw := by
  induction gs generalizing raw with
  | nil => simp at hg
  | cons t ts ih =>
    rcases fresh with ⟨ft,fs⟩
    rcases List.mem_cons.mp hg with e|h
    · exact e ▸ ft
    · exact fun hRaw => ih fs h (List.mem_cons_of_mem _ hRaw)

end CoThetaFreeCore
namespace CoThetaFreeCore

def pairCode (op : Kind) (sw : Bool) (u v : Bool) : Bool :=
  if sw then applyKind op v u else applyKind op u v

theorem pair_collision (A B : Kind) : ∀ (sa sb : Bool),
    ∃ a b c d : Bool, (a,b)≠(c,d) ∧
      pairCode A sa a b=pairCode A sa c d ∧ pairCode B sb a b=pairCode B sb c d := by
  cases A <;> cases B <;> decide

theorem joint_reader_code {ρ : Type} (x y : ρ→Bool) (different : x≠y) (g : TraceGate ρ)
    (rx : reads g x) (ry : reads g y) :
    ∃ sw : Bool, ∀ i, g.value i=pairCode g.kind sw (x i) (y i) := by
  rcases rx with xl|xr <;> rcases ry with yl|yr
  · exact (different (xl.symm.trans yl)).elim
  · exact ⟨false,by simp [TraceGate.value,pairCode,xl,yr]⟩
  · exact ⟨true,by simp [TraceGate.value,pairCode,xr,yl]⟩
  · exact (different (xr.symm.trans yr)).elim

theorem two_joint_readers_impossible {ρ τ : Type} (x y out : ρ→Bool)
    (raw : List (ρ→Bool)) (gs : List (TraceGate ρ)) (A B : TraceGate ρ)
    (rxA : reads A x) (ryA : reads A y) (rxB : reads B x) (ryB : reads B y)
    (different : x≠y) (notPrimary : out≠x ∧ out≠y)
    (well : registered raw gs) (available : out∈traceWires raw gs)
    (point : Bool→Bool→τ→ρ)
    (px : ∀ a b j, x (point a b j)=a)
    (py : ∀ a b j, y (point a b j)=b)
    (fixed : ∀ a b c d j, agreeOutside (fun f => f=x ∨ f=y) (point a b j) (point c d j) raw)
    (separate : ∀ a b c d : Bool, (a,b)≠(c,d) → ∃ j : τ, out (point a b j)≠out (point c d j)) :
    ∃ g∈gs, (reads g x ∨ reads g y) ∧ g≠A ∧ g≠B := by
  classical
  obtain ⟨sa,saCode⟩ := joint_reader_code x y different A rxA ryA
  obtain ⟨sb,sbCode⟩ := joint_reader_code x y different B rxB ryB
  obtain ⟨a,b,c,d,ne,ca,cb⟩ := pair_collision A.kind B.kind sa sb
  obtain ⟨j,away⟩ := separate a b c d ne
  have eA : A.value (point a b j)=A.value (point c d j) := by
    simpa only [saCode,px,py] using ca
  have eB : B.value (point a b j)=B.value (point c d j) := by
    simpa only [sbCode,px,py] using cb
  have badOut : ¬(out=x ∨ out=y) := fun e => e.elim notPrimary.1 notPrimary.2
  obtain ⟨g,hg,read,diff⟩ := reader_witness (fun f => f=x ∨ f=y) _ _ well
    (fixed a b c d j) available badOut away
  refine ⟨g,hg,?_,fun eq => diff (eq ▸ eA),fun eq => diff (eq ▸ eB)⟩
  rcases read with (h|h)|(h|h)
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inr h)

end CoThetaFreeCore


namespace CoPetersenThetaGeometry

def nine (m : Nat) : Bool :=
  let x := m.testBit
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def theta (m : Nat) : Bool :=
  let x := m.testBit
  (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 3 && x 4) ||
  (x 1 && x 4) || (x 0 && x 5) || (x 5 && x 6) || (x 1 && x 6)

def embedding (j : Fin 6) : List Nat := match j.val with
  | 0 => [2, 8, 3, 1, 6, 7, 5]
  | 1 => [3, 5, 8, 2, 7, 4, 0]
  | 2 => [8, 0, 5, 3, 4, 6, 1]
  | 3 => [5, 1, 0, 8, 6, 7, 2]
  | 4 => [0, 2, 1, 5, 7, 4, 3]
  | _ => [1, 3, 2, 0, 4, 6, 8]

def cycleEnd (j : Fin 6) : Nat := match j.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 8
  | _ => 5

def subEnd (j : Fin 6) : Nat := match j.val with
  | 0 => 4
  | 1 => 6
  | 2 => 7
  | 3 => 4
  | 4 => 6
  | _ => 7

def outerNeighbor (j : Fin 6) : Nat := match j.val with
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 8
  | 4 => 5
  | _ => 0

def shortNeighbor (j : Fin 6) : Nat := match j.val with
  | 0 => 3
  | 1 => 8
  | 2 => 5
  | 3 => 0
  | 4 => 1
  | _ => 2

def sensitive : List Nat := [2, 0, 16, 2, 2, 20, 2, 10, 2, 16, 2, 32, 2, 80, 2, 130, 2, 258, 4, 1, 1, 0, 1, 4, 1, 9, 1, 20, 1, 36, 1, 64, 1, 129, 1, 257, 2, 9, 8, 2, 2, 0, 2, 8, 2, 18, 2, 34, 2, 72, 2, 128, 2, 258, 4, 5, 4, 18, 16, 4, 4, 0, 4, 16, 4, 36, 4, 68, 4, 144, 4, 256, 8, 1, 1, 10, 1, 5, 1, 8, 1, 0, 1, 40, 1, 65, 1, 129, 1, 257, 128, 1, 1, 130, 1, 5, 1, 9, 1, 144, 1, 0, 1, 65, 1, 128, 1, 256, 2, 257, 256, 2, 2, 260, 2, 10, 2, 18, 2, 34, 2, 0, 2, 130, 2, 256, 4, 5, 4, 34, 32, 4, 4, 40, 4, 20, 4, 32, 4, 68, 4, 0, 4, 260, 8, 9, 8, 10, 8, 36, 32, 8, 8, 48, 8, 32, 8, 64, 8, 136, 8, 0]

def plant (j : Fin 6) (m : Nat) : Nat :=
  (List.range 7).foldl (fun val i => if m.testBit i then
    val ||| (1 <<< ((embedding j).getD i 0)) else val) 0

theorem theta_slice : ∀ (j : Fin 6) (r : Fin 128),
    nine (plant j r.val) = theta r.val ∧
    (plant j r.val).testBit (cycleEnd j)=false ∧
    (plant j r.val).testBit (subEnd j)=false := by decide +kernel

theorem every_input_has_slice : ∀ v : Fin 9, ∃ j : Fin 6,
    cycleEnd j=v.val ∨ subEnd j=v.val := by decide

def sensRow (p q : Fin 9) (v : Bool) : Nat :=
  sensitive.getD (2*(9*p.val+q.val)+v.toNat) 0

theorem sensitive_at_both : ∀ (p q : Fin 9), p≠q → ∀ v : Bool,
    let r := sensRow p q v
    r.testBit p.val=false ∧ r.testBit q.val=v ∧
    nine r=false ∧ nine (r ||| (1 <<< p.val))=true := by decide +kernel

def panel (p q : Bool) : Bool × Bool × Bool := (p&&q,(p&&q)||p,(p&&q)||q)

theorem slice_panels : ∀ (j : Fin 6) (p q : Bool),
    let r := (if p then 1 <<< cycleEnd j else 0) ||| (if q then 1 <<< subEnd j else 0)
    (nine r, nine (r ||| (1 <<< outerNeighbor j)), nine (r ||| (1 <<< shortNeighbor j))) = panel p q := by
  decide +kernel

inductive Kind where | conj | disj | leftOnly | rightOnly
def binary : Kind → Bool → Bool → Bool
  | .conj,a,b => a&&b
  | .disj,a,b => a||b
  | .leftOnly,a,b => a && !b
  | .rightOnly,a,b => !a && b

theorem unbalanced_code (kind : Kind) : ∀ (a b c d : Bool),
    ¬[(binary kind false false,a),(binary kind false true,b),
      (binary kind true false,c),(binary kind true true,d)].Nodup := by
  cases kind <;> decide

end CoPetersenThetaGeometry
namespace CoThetaNine
open CoThetaFreeCore
open CoPetersenThetaGeometry (nine sensRow cycleEnd subEnd outerNeighbor shortNeighbor)

abbrev Input := Fin 512
def vtx (i : Fin 9) (r : Input) : Bool := r.val.testBit i.val
def ans (r : Input) : Bool := nine r.val
def vertices : List (Input→Bool) := absentBit::List.ofFn vtx

def row (n : Nat) : Input := ⟨n % 512,Nat.mod_lt _ (by decide)⟩
def index (n : Nat) : Fin 9 := ⟨n % 9,Nat.mod_lt _ (by decide)⟩
def ep (j : Fin 6) := index (cycleEnd j)
def eqp (j : Fin 6) := index (subEnd j)
def low (p q : Fin 9) (v : Bool) : Input := row (sensRow p q v)
def high (p q : Fin 9) (v : Bool) : Input := row ((low p q v).val ||| (1 <<< p.val))

theorem sens_data : ∀ (p q : Fin 9), p≠q → ∀ b : Bool,
    vtx p (low p q b)=false ∧ vtx p (high p q b)=true ∧
    vtx q (low p q b)=b ∧ vtx q (high p q b)=b ∧
    ans (low p q b)≠ans (high p q b) ∧
    ∀ t : Fin 9, t≠p → vtx t (low p q b)=vtx t (high p q b) := by decide +kernel

theorem distinct_raw : ∀ i j : Fin 9, i≠j → ∃ r : Input, vtx i r≠vtx j r := by
  decide +kernel

theorem not_raw : ∀ i : Fin 9, ∃ r : Input, ans r≠vtx i r := by decide +kernel

theorem distinct_inputs {i j : Fin 9} (ne : i≠j) : vtx i≠vtx j := by
  obtain ⟨r,d⟩ := distinct_raw i j ne
  exact fun h => d (congrFun h r)

theorem not_input (i : Fin 9) : ans≠vtx i := by
  obtain ⟨r,d⟩ := not_raw i
  exact fun h => d (congrFun h r)

theorem agree_on_vertices (E : (Input→Bool)→Prop) (r s : Input)
    (ok : ∀ i : Fin 9, ¬E (vtx i) → vtx i r=vtx i s) :
    agreeOutside E r s vertices := by
  intro w hw h
  rcases List.mem_cons.mp hw with z|h2
  · subst w
    rfl
  · obtain ⟨i,hi⟩ := List.mem_ofFn.mp h2
    subst w
    exact ok i h

def point (j : Fin 6) (a b : Bool) (t : Fin 3) : Input :=
  let u := (if a then 1 <<< cycleEnd j else 0) ||| (if b then 1 <<< subEnd j else 0)
  row (match t.val with
    | 0 => u
    | 1 => u ||| (1 <<< outerNeighbor j)
    | _ => u ||| (1 <<< shortNeighbor j))

theorem panel_data : ∀ (j : Fin 6), ep j≠eqp j ∧
    (∀ a b t, vtx (ep j) (point j a b t)=a ∧ vtx (eqp j) (point j a b t)=b) ∧
    (∀ a b c d t, ∀ i : Fin 9, i≠ep j → i≠eqp j →
      vtx i (point j a b t)=vtx i (point j c d t)) ∧
    (∀ a b c d : Bool, (a,b)≠(c,d) → ∃ t : Fin 3, ans (point j a b t)≠ans (point j c d t)) := by
  decide +kernel

theorem third_joint_reader (j : Fin 6) (gs : List (TraceGate Input)) (A B : TraceGate Input)
    (rxA : reads A (vtx (ep j))) (ryA : reads A (vtx (eqp j)))
    (rxB : reads B (vtx (ep j))) (ryB : reads B (vtx (eqp j)))
    (well : registered vertices gs) (out : ans∈traceWires vertices gs) :
    ∃ g∈gs, (reads g (vtx (ep j)) ∨ reads g (vtx (eqp j))) ∧ g≠A ∧ g≠B := by
  obtain ⟨distinct,axis,other,apart⟩ := panel_data j
  apply two_joint_readers_impossible (vtx (ep j)) (vtx (eqp j)) ans vertices gs A B
    rxA ryA rxB ryB (distinct_inputs distinct) ⟨not_input _,not_input _⟩ well out
    (point j) (fun a b t => (axis a b t).1) (fun a b t => (axis a b t).2) _ apart
  intro a b c d t
  apply agree_on_vertices
  intro i ni
  exact other a b c d t i (fun e => ni (Or.inl (congrArg vtx e)))
    (fun e => ni (Or.inr (congrArg vtx e)))

theorem masks_some_value (op : CoThetaFreeCore.Kind) : ∀ sw : Bool, ∃ v : Bool,
    ∀ a b : Bool, pairCode op sw a v=pairCode op sw b v := by
  cases op <;> decide

theorem another_raw_reader {p q : Fin 9} (ne : p≠q) (gs : List (TraceGate Input))
    (gate : TraceGate Input) (rx : reads gate (vtx p)) (ry : reads gate (vtx q))
    (well : registered vertices gs) (out : ans∈traceWires vertices gs) :
    ∃ g∈gs, reads g (vtx p) ∧ g≠gate := by
  obtain ⟨sw,code⟩ := joint_reader_code _ _ (distinct_inputs ne) gate rx ry
  obtain ⟨b,masked⟩ := masks_some_value gate.kind sw
  obtain ⟨pl,ph,ql,qh,diff,fixed⟩ := sens_data p q ne b
  have source : agreeOutside (fun w => w=vtx p) (low p q b) (high p q b) vertices := by
    apply agree_on_vertices
    intro i ni
    exact fixed i (fun e => ni (congrArg vtx e))
  have mask : gate.value (low p q b)=gate.value (high p q b) := by
    simpa only [code,pl,ph,ql,qh] using masked false true
  exact second_reader (vtx p) (low p q b) (high p q b) gate well source out (not_input p) diff mask

end CoThetaNine
namespace CoThetaNine
open CoThetaFreeCore

def neighborIndex (p : Fin 9) := index (p.val+1)
theorem neighbor_diff : ∀ p : Fin 9, p≠neighborIndex p := by decide

theorem a_raw_reader (p : Fin 9) {gs : List (TraceGate Input)}
    (well : registered vertices gs) (out : ans∈traceWires vertices gs) :
    ∃ g∈gs, reads g (vtx p) := by
  let q := neighborIndex p
  have ne : p≠q := neighbor_diff p
  obtain ⟨_,_,_,_,diff,fix⟩ := sens_data p q ne false
  have source : agreeOutside (fun w => w=vtx p) (low p q false) (high p q false) vertices := by
    apply agree_on_vertices
    intro i ni
    exact fix i (fun e => ni (congrArg vtx e))
  obtain ⟨g,hg,h,_⟩ := reader_witness (·=vtx p) _ _ well source out (not_input p) diff
  exact ⟨g,hg,h⟩

def ThreeReaders {ρ : Type} (P : TraceGate ρ→Prop) (gs : List (TraceGate ρ)) : Prop :=
  ∃ A∈gs, ∃ B∈gs, ∃ C∈gs, P A ∧ P B ∧ P C ∧ A≠B ∧ A≠C ∧ B≠C

theorem three_for_pair (j : Fin 6) {gs : List (TraceGate Input)}
    (well : registered vertices gs) (out : ans∈traceWires vertices gs)
    (known : (∃ A∈gs, ∃ B∈gs, reads A (vtx (ep j)) ∧ reads B (vtx (ep j)) ∧ A≠B) ∨
             (∃ A∈gs, ∃ B∈gs, reads A (vtx (eqp j)) ∧ reads B (vtx (eqp j)) ∧ A≠B)) :
    ThreeReaders (fun g => reads g (vtx (ep j)) ∨ reads g (vtx (eqp j))) gs := by
  classical
  have ne := (panel_data j).1
  by_cases shared : ∃ J∈gs, reads J (vtx (ep j)) ∧ reads J (vtx (eqp j))
  · obtain ⟨J,hJ,Jp,Jq⟩ := shared
    obtain ⟨A,hA,Ap,AJ⟩ := another_raw_reader ne gs J Jp Jq well out
    obtain ⟨B,hB,Bq,BJ⟩ := another_raw_reader ne.symm gs J Jq Jp well out
    by_cases e : A=B
    · subst B
      obtain ⟨C,hC,read,CJ,CA⟩ := third_joint_reader j gs J A Jp Jq Ap Bq well out
      exact ⟨J,hJ,A,hA,C,hC,Or.inl Jp,Or.inl Ap,read,AJ.symm,CJ.symm,CA.symm⟩
    · exact ⟨J,hJ,A,hA,B,hB,Or.inl Jp,Or.inl Ap,Or.inr Bq,AJ.symm,BJ.symm,e⟩
  · rcases known with ⟨A,hA,B,hB,Ap,Bp,AB⟩|⟨A,hA,B,hB,Aq,Bq,AB⟩
    · obtain ⟨C,hC,Cq⟩ := a_raw_reader (eqp j) well out
      exact ⟨A,hA,B,hB,C,hC,Or.inl Ap,Or.inl Bp,Or.inr Cq,AB,
        fun e => shared ⟨A,hA,Ap,e ▸ Cq⟩,fun e => shared ⟨B,hB,Bp,e ▸ Cq⟩⟩
    · obtain ⟨C,hC,Cp⟩ := a_raw_reader (ep j) well out
      exact ⟨A,hA,B,hB,C,hC,Or.inr Aq,Or.inr Bq,Or.inl Cp,AB,
        fun e => shared ⟨A,hA,e ▸ Cp,Aq⟩,fun e => shared ⟨B,hB,e ▸ Cp,Bq⟩⟩

end CoThetaNine
namespace CoThetaFreeCore

theorem fresh_ports {ρ : Type} {ws : List (ρ→Bool)} (g : TraceGate ρ)
    (hl : g.left∈ws) (hr : g.right∈ws) (hz : absentBit∈ws) (fresh : g.value∉ws) :
    g.left≠absentBit ∧ g.right≠absentBit ∧ g.left≠g.right := by
  refine ⟨?_,?_,?_⟩
  · intro e
    apply fresh
    change (fun i => applyKind g.kind (g.left i) (g.right i))∈ws
    rw [e]
    rcases zero_left g.kind g.right with er|ez
    · exact (congrArg (fun v => v∈ws) er).mpr hr
    · exact (congrArg (fun v => v∈ws) ez).mpr hz
  · intro e
    apply fresh
    change (fun i => applyKind g.kind (g.left i) (g.right i))∈ws
    rw [e]
    rcases zero_right g.kind g.left with er|ez
    · exact (congrArg (fun v => v∈ws) er).mpr hl
    · exact (congrArg (fun v => v∈ws) ez).mpr hz
  · intro e
    apply fresh
    change (fun i => applyKind g.kind (g.left i) (g.right i))∈ws
    rw [e]
    rcases same_result g.kind g.right with er|ez
    · exact (congrArg (fun v => v∈ws) er).mpr hr
    · exact (congrArg (fun v => v∈ws) ez).mpr hz

noncomputable def vanishing {ρ σ : Type} (lift : σ→ρ) (gs : List (TraceGate ρ)) :=
  gs.filter (fun g => @decide (disappears lift g) (Classical.propDecidable _))

theorem saved_eq_length {ρ σ : Type} (lift : σ→ρ) (gs : List (TraceGate ρ)) :
    saved lift gs = (vanishing lift gs).length := by
  classical
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    by_cases h : disappears lift g <;> simp [saved,vanishing,h] at * <;> omega

end CoThetaFreeCore

namespace CoThetaNine
open CoThetaFreeCore

theorem endpoint_in_slice : ∀ p : Fin 9, ∃ j : Fin 6, p=ep j ∨ p=eqp j := by decide

theorem ans_not_zero : ans≠absentBit := by
  intro e
  have bad := congrFun e (row 3)
  have test : ans (row 3)=true := by decide
  exact Bool.noConfusion (test.symm.trans bad)

theorem fresh_slice_head {g : TraceGate Input} {tail : List (TraceGate Input)}
    (h : sufficient vertices ans (g::tail)) (fresh : freshTrace vertices (g::tail)) :
    ∃ j : Fin 6, ThreeReaders (fun t => reads t (vtx (ep j)) ∨ reads t (vtx (eqp j))) (g::tail) := by
  obtain ⟨nonL,nonR,different⟩ := fresh_ports g h.1.1 h.1.2.1 (List.mem_cons_self) fresh.1
  have rawL := (List.mem_cons.mp h.1.1).resolve_left nonL
  have rawR := (List.mem_cons.mp h.1.2.1).resolve_left nonR
  obtain ⟨x,ex⟩ := List.mem_ofFn.mp rawL
  obtain ⟨y,ey⟩ := List.mem_ofFn.mp rawR
  have xy : x≠y := fun eq => different (ex.symm.trans ((congrArg vtx eq).trans ey))
  have rx : reads g (vtx x) := Or.inl ex.symm
  have ry : reads g (vtx y) := Or.inr ey.symm
  obtain ⟨s,hs,sx,other⟩ := another_raw_reader xy _ g rx ry h.1 h.2
  obtain ⟨j,side⟩ := endpoint_in_slice x
  refine ⟨j,three_for_pair j h.1 h.2 ?_⟩
  rcases side with eq|eq
  · exact Or.inl ⟨g,List.mem_cons_self,s,hs,eq ▸ rx,eq ▸ sx,other.symm⟩
  · exact Or.inr ⟨g,List.mem_cons_self,s,hs,eq ▸ rx,eq ▸ sx,other.symm⟩

theorem nonempty_solution {gs : List (TraceGate Input)} (h : sufficient vertices ans gs) : gs≠[] := by
  intro e
  subst gs
  have m : ans∈vertices := h.2
  rcases List.mem_cons.mp m with z|r
  · exact ans_not_zero z
  · obtain ⟨i,eq⟩ := List.mem_ofFn.mp r
    exact not_input i eq.symm

end CoThetaNine
namespace CoThetaBits
open CoThetaFreeCore

abbrev Width := 411
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

def raw : List Wire := [(0x180001c003801c3c000006007f81f80ffe1fffc00007001f807f03ff00fffffc700383e000e1fffe003803fffffffc001fff,0x1200008001001424404004802b80a809160939484001000980450089008c583820028220826093ca11080a28aa181401444a),
(0xe00006001c001fc00000380081fe7ff00fe01ffff0180067ff80fd87ff07f0038003fc0000fe00fffffffc1fe003ffffe000,0x2000020104000d4002800800008a18d002a00382e0080822988055832903609080019400142a021c45994c12c0501825800c),
(0x7f0003f8001fffe000001fc000fe0780000fffe0000fe000780000fe07fff80003fffc000000ffff00003fffe00003ffffffff,0x5b0422d8221af740008415c120d4050404495640100ae050504220aa04d25001035fa8408120956401202691440483e3da1bb0),
(0x7800003ffffe0000000001fffff0007fffff00000000fffff800000fff800000003ffffffffff000000003ffffffffc00000000,0x28000836f73a022000108065a31000756e660040020832a9c801000cf5060020001953118ca380800100637e19714e0408c0220),
(0x7fffffc000000000000001ffffffff80000000000000fffffffffff000000000003ffffffffffffffffffc00000000000000000,0x56ddf340004004400021018a5c6e7500008001810000c55615d63760000800002226ac26315c0d1f8e1b80002080300821010c0),
(0x7ffffffffffffffffffffe0000000000000000000000ffffffffffffffffffffffc000000000000000000000000000000000000,0x18e68387247cc8789881f00000400000080008002030f9e7e767c38f366fc6383c00300000600004000c0030010040100e00300),
(0x7fffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000,0x67097c385b813781233e01f37f8f965e70f8d1f9c3c000080000040000000840c000c0000180001808100040000180203001c00)]

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
  | 1 => 17
  | 2 => 1
  | 3 => 35
  | 4 => 71
  | 5 => 147
  | _ => 237

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
  simp [CoThetaFreeCore.norm,low_raw j,phase]

theorem no_small_ordinary (certificate : certifiedSearch 10 raw=false)
    {n ws} (program : Ordinary start n ws) (cost : n≤10) (out : den target∈ws) : False := by
  obtain ⟨ys,fre,contains⟩ := simulate_all_wires empty program
  have self : norm empty (den target)=den target := by
    funext r
    simp [CoThetaFreeCore.norm,den_target,empty,phase]
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

theorem Free.map_rows {ρ σ : Type} (lift : σ→ρ)
    {init ws n} (run : @Free ρ init n ws) :
    Free (init.map (restrict lift)) n (ws.map (restrict lift)) := by
  induction run with
  | start => exact Free.start
  | @binary n ws a b pre kind ha hb ih =>
    have h1 := List.mem_map_of_mem (f:=restrict lift) ha
    have h2 := List.mem_map_of_mem (f:=restrict lift) hb
    exact Free.binary ih kind h1 h2

end CoThetaFreeCore

namespace CoThetaNine
open CoThetaFreeCore

abbrev SmallInput := Fin 128
def raw7 (i : Fin 7) (r : SmallInput) : Bool := r.val.testBit i.val
def ans7 (r : SmallInput) : Bool := CoPetersenThetaGeometry.theta r.val
def vertices7 : List (SmallInput→Bool) := absentBit::List.ofFn raw7
def sliceLift (j : Fin 6) (r : SmallInput) : Input := row (CoPetersenThetaGeometry.plant j r.val)

def coord7 (j : Fin 6) (v : Fin 9) : Option (Fin 7) :=
  match j.val,v.val with
  | 0,2 => some 0
  | 0,8 => some 1
  | 0,3 => some 2
  | 0,1 => some 3
  | 0,6 => some 4
  | 0,7 => some 5
  | 0,5 => some 6
  | 1,3 => some 0
  | 1,5 => some 1
  | 1,8 => some 2
  | 1,2 => some 3
  | 1,7 => some 4
  | 1,4 => some 5
  | 1,0 => some 6
  | 2,8 => some 0
  | 2,0 => some 1
  | 2,5 => some 2
  | 2,3 => some 3
  | 2,4 => some 4
  | 2,6 => some 5
  | 2,1 => some 6
  | 3,5 => some 0
  | 3,1 => some 1
  | 3,0 => some 2
  | 3,8 => some 3
  | 3,6 => some 4
  | 3,7 => some 5
  | 3,2 => some 6
  | 4,0 => some 0
  | 4,2 => some 1
  | 4,1 => some 2
  | 4,5 => some 3
  | 4,7 => some 4
  | 4,4 => some 5
  | 4,3 => some 6
  | 5,1 => some 0
  | 5,3 => some 1
  | 5,2 => some 2
  | 5,0 => some 3
  | 5,4 => some 4
  | 5,6 => some 5
  | 5,8 => some 6
  | _,_ => none

theorem slice7_values : ∀(j : Fin 6) (r : SmallInput),
    ans (sliceLift j r)=ans7 r ∧ vtx (ep j) (sliceLift j r)=false ∧
    vtx (eqp j) (sliceLift j r)=false ∧
    ∀ i : Fin 9, vtx i (sliceLift j r)=
      match coord7 j i with | none => false | some k => raw7 k r := by decide +kernel

theorem slice_known (j : Fin 6) : ∀ w∈vertices, restrict (sliceLift j) w∈vertices7 := by
  intro w hw
  rcases List.mem_cons.mp hw with z|r
  · subst w
    exact List.mem_cons_self
  · obtain ⟨i,e⟩ := List.mem_ofFn.mp r
    subst w
    cases h : coord7 j i with
    | none =>
      have eq : restrict (sliceLift j) (vtx i)=absentBit := by
        funext r
        simpa [restrict,h,absentBit] using (slice7_values j r).2.2.2 i
      exact eq ▸ List.mem_cons_self
    | some k =>
      have eq : restrict (sliceLift j) (vtx i)=raw7 k := by
        funext r
        simpa [restrict,h] using (slice7_values j r).2.2.2 i
      exact eq ▸ List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨k,rfl⟩)

def packBits (a b c d e f g : Bool) : SmallInput :=
  ⟨(a.toNat+2*b.toNat+4*c.toNat+8*d.toNat+16*e.toNat+32*f.toNat+64*g.toNat) % 128,
    Nat.mod_lt _ (by decide)⟩

def pack (x : Fin 7 → Bool) : SmallInput := packBits (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

theorem pack_exact : ∀ a b c d e f g : Bool,
    let t := packBits a b c d e f g
    (raw7 0 t,raw7 1 t,raw7 2 t,raw7 3 t,raw7 4 t,raw7 5 t,raw7 6 t)=(a,b,c,d,e,f,g) := by
  intro a b c d e f g
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> rfl

theorem unpack (x : Fin 7→Bool) (j : Fin 7) : raw7 j (pack x)=x j := by
  have h := pack_exact (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)
  change (_,_,_,_,_,_,_) = (_,_,_,_,_,_,_) at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨e0,e1,e2,e3,e4,e5,e6⟩ := h
  have total : ∀ t : Fin 7, t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 := by decide
  rcases total j with e|e|e|e|e|e|e <;> subst j <;> assumption

theorem numeric_goal (r : SmallInput) : ans7 r=CoThetaFreeCore.theta (fun j => raw7 j r) := by
  rfl

def toRows (r : CoThetaBits.Row) := pack (CoThetaBits.sample r)

theorem numeric_target : restrict toRows ans7=CoThetaBits.den CoThetaBits.target := by
  funext r
  change ans7 (toRows r)=_
  rw [numeric_goal]
  have eq : (fun j => raw7 j (toRows r))=CoThetaBits.sample r :=
    funext (unpack (CoThetaBits.sample r))
  rw [eq]
  exact CoThetaBits.sample_correct r

theorem numeric_lower (cert : CoThetaBits.certifiedSearch 10 CoThetaBits.raw=false)
    {n ws} (run : Free vertices7 n ws) (goal : ans7∈ws) : 11≤n := by
  classical
  obtain ⟨m,S,le,live,sub⟩ := rewind (run.map_rows toRows) List.mem_cons_self
    (Live.stop (goal:=CoThetaBits.den CoThetaBits.target)) (by
      intro w e
      have h := List.mem_map_of_mem (f:=restrict toRows) goal
      rw [numeric_target] at h
      exact e ▸ h)
  have rep := CoThetaBits.root_rep live (by
    intro f h
    have w := sub f h
    obtain ⟨g,hg,eq⟩ := List.mem_map.mp w
    subst f
    rcases List.mem_cons.mp hg with z|other
    · subst g
      exact Or.inl rfl
    · obtain ⟨j,eq⟩ := List.mem_ofFn.mp other
      subst g
      exact Or.inr ⟨j,funext (fun r => (unpack (CoThetaBits.sample r) j).symm)⟩)
  apply Classical.byContradiction
  intro bad
  have pass := CoThetaBits.certified_complete live 10 (by omega) _ CoThetaBits.raw_nodup rep
  exact Bool.false_ne_true (cert.symm.trans pass)

end CoThetaNine
namespace CoThetaNine
open CoThetaFreeCore

def SignedLower : Prop := ∀ {n ws}, Free vertices7 n ws → ans7∈ws → 11≤n

theorem three_saved (j : Fin 6) {gs : List (TraceGate Input)}
    (three : ThreeReaders (fun g => reads g (vtx (ep j)) ∨ reads g (vtx (eqp j))) gs) :
    3≤saved (sliceLift j) gs := by
  classical
  obtain ⟨A,hA,B,hB,C,hC,rA,rB,rC,AB,AC,BC⟩ := three
  have zp : restrict (sliceLift j) (vtx (ep j))=absentBit :=
    funext (fun r => (slice7_values j r).2.1)
  have zq : restrict (sliceLift j) (vtx (eqp j))=absentBit :=
    funext (fun r => (slice7_values j r).2.2.1)
  have retain (g : TraceGate Input) (hg : g∈gs) (r : reads g (vtx (ep j)) ∨ reads g (vtx (eqp j))) :
      g∈vanishing (sliceLift j) gs := by
    have d : disappears (sliceLift j) g := r.elim (reading_zero_disappears _ zp) (reading_zero_disappears _ zq)
    simp [vanishing,hg,d]
  have nd : [A,B,C].Nodup := by simp [AB,AC,BC]
  have sub : ∀ t∈[A,B,C],t∈vanishing (sliceLift j) gs := by
    intro t h
    rcases List.mem_cons.mp h with e|h
    · exact e ▸ retain A hA rA
    rcases List.mem_cons.mp h with e|h
    · exact e ▸ retain B hB rB
    rcases List.mem_cons.mp h with e|h
    · exact e ▸ retain C hC rC
    · simp at h
  rw [saved_eq_length]
  exact length_of_cover [A,B,C] _ nd sub

theorem residual_at_least_eleven (cert : SignedLower)
    (j : Fin 6) {gs : List (TraceGate Input)} (ok : sufficient vertices ans gs) :
    11≤remaining (sliceLift j) gs := by
  obtain ⟨ws,run,sub⟩ := restrict_trace (sliceLift j) gs ok.1
    (Free.start (raw:=vertices7)) List.mem_cons_self (slice_known j)
  have read := sub ans ok.2
  have ax : restrict (sliceLift j) ans=ans7 := funext (fun r => (slice7_values j r).1)
  rw [ax] at read
  simpa only [Nat.zero_add] using cert run read

theorem any_nine_lower (cert : SignedLower)
    {gs : List (TraceGate Input)} (ok : sufficient vertices ans gs) : 14≤gs.length := by
  classical
  obtain ⟨ts,solves,fresh,le,_⟩ := simplify_trace gs ok
  cases ts with
  | nil => exact (nonempty_solution solves rfl).elim
  | cons g tail =>
    obtain ⟨j,readers⟩ := fresh_slice_head solves fresh
    have gain := three_saved j readers
    have cost := residual_at_least_eleven cert j solves
    have eq := accounted (sliceLift j) (g::tail)
    omega

end CoThetaNine
namespace CoNatBench
abbrev Word := Nat × Nat
def project (w : CoThetaBits.Wire) : Word := (w.1.toNat,w.2.toNat)
def target := project CoThetaBits.target
def all := target.1
def sep (w : Word) := w.1 ^^^ w.2
def meet (a b : Word) : Word := (a.1 &&& b.1,a.2 &&& b.2)
def join (a b : Word) : Word := (a.1 ||| b.1,a.2 ||| b.2)
def skip (a b : Word) : Word := (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
def cover (ws : List Word) := ws.foldl (fun c w => c ||| sep w) 0
def pairs {α : Type} (f : α → α → Bool) : List α → Bool
  | [] => false
  | x::xs => xs.any (f x) || pairs f xs
def successors (k : Nat) (next : List Word→Bool) (ws : List Word) : Bool :=
  let n := ws.length
  if n>k+2 then false else
  pairs (fun a b =>
    let rest := ws.filter (fun w => w != a && w != b)
    let base := cover rest
    let ca := base ||| sep a
    let cb := base ||| sep b
    let stay := n+1≤k+1
    let half := n≤k+1
    ([meet a b,join a b,skip a b,skip b a] : List Word).any fun z =>
      z != (0,0) && !(ws.contains z) &&
        (let cut := sep z
         ((base ||| cut)==all && next (z::rest)) ||
         (half && (ca ||| cut)==all && next (z::a::rest)) ||
         (half && (cb ||| cut)==all && next (z::b::rest)) ||
         (stay && next (z::a::b::rest)))) ws

def search : Nat → List Word → Bool
  | 0,ws => ws.contains target
  | k+1,ws => ws.contains target || successors k (search k) ws
end CoNatBench
namespace CoNatBench

def multiplicities : List Word → Nat×Nat
  | [] => (0,0)
  | w::ws =>
    let s := sep w
    let m := multiplicities ws
    (s ||| m.1, (s &&& m.1) ||| m.2)

def guarded (k : Nat) (next : List Word→Bool) (ws : List Word) : Bool :=
  let n := ws.length
  if n>k+2 then false else
  let bucket := multiplicities ws
  let once := bucket.1 ^^^ bucket.2
  let cols := ws.map fun w => (w,sep w &&& once)
  let half := n≤k+1
  let stay := n≤k
  pairs (fun a b =>
    let a0 := (a.2 &&& b.1.1)==0
    let a1 := (a.2 &&& b.1.1)==a.2
    let b0 := (b.2 &&& a.1.1)==0
    let b1 := (b.2 &&& a.1.1)==b.2
    let rest := ws.filter (fun w => w != a.1 && w != b.1)
    let base := cover rest
    let attempt (oka okb : Bool) (value : Unit → Word) :=
      (stay || (half && (oka || okb)) || (oka && okb)) &&
        (let z := value ()
         z != (0,0) && !(ws.contains z) &&
          ((oka && okb && (base ||| sep z)==all && next (z::rest)) ||
           (half && okb && next (z::a.1::rest)) ||
           (half && oka && next (z::b.1::rest)) ||
           (stay && next (z::a.1::b.1::rest))))
    attempt a1 b1 (fun _ => meet a.1 b.1) ||
      attempt a0 b0 (fun _ => join a.1 b.1) ||
      attempt a0 b1 (fun _ => skip a.1 b.1) ||
      attempt a1 b0 (fun _ => skip b.1 a.1)) cols

def guardedSearch : Nat → List Word → Bool
  | 0,ws => ws.contains target
  | k+1,ws => ws.contains target || guarded k (guardedSearch k) ws

end CoNatBench
namespace CoNatBench
open CoThetaFreeCore

private theorem foldBits (ws : List Word) (i : Nat) (seed : Nat) :
    (ws.foldl (fun c w => c ||| sep w) seed).testBit i =
    (seed.testBit i || ws.any (fun w => (sep w).testBit i)) := by
  induction ws generalizing seed with
  | nil => simp
  | cons a xs ih =>
    simp [List.foldl_cons,ih,Nat.testBit_or,Bool.or_assoc]

theorem covered_iff (ws : List Word) (i : Nat) :
    (cover ws).testBit i=true ↔ ∃ w∈ws,(sep w).testBit i=true := by
  simp [cover,foldBits,List.any_eq_true]

private theorem firstMask (ws : List Word) (i : Nat) (w : Word)
    (h : w∈ws) (bit : (sep w).testBit i=true) : (multiplicities ws).1.testBit i=true := by
  induction ws with
  | nil => simp at h
  | cons a xs ih =>
    change (sep a ||| (multiplicities xs).1).testBit i=true
    rw [Nat.testBit_or,Bool.or_eq_true]
    rcases List.mem_cons.mp h with e|h
    · exact Or.inl (e ▸ bit)
    · exact Or.inr (ih h)

private theorem secondMask (ws : List Word) (i : Nat) {a b : Word} (ab : a≠b)
    (ha : a∈ws) (hb : b∈ws) (da : (sep a).testBit i=true) (db : (sep b).testBit i=true) :
    (multiplicities ws).2.testBit i=true := by
  induction ws with
  | nil => simp at ha
  | cons h xs ih =>
    change ((sep h &&& (multiplicities xs).1) ||| (multiplicities xs).2).testBit i=true
    rw [Nat.testBit_or,Bool.or_eq_true]
    by_cases x : a=h
    · subst h
      have bt := (List.mem_cons.mp hb).resolve_left ab.symm
      exact Or.inl (by simp [Nat.testBit_and,da,firstMask xs i b bt db])
    · have atail := (List.mem_cons.mp ha).resolve_left x
      by_cases y : b=h
      · subst h
        exact Or.inl (by simp [Nat.testBit_and,db,firstMask xs i a atail da])
      · exact Or.inr (ih atail ((List.mem_cons.mp hb).resolve_left y))

def privateMask (ws : List Word) (a : Word) :=
  sep a &&& ((multiplicities ws).1 ^^^ (multiplicities ws).2)

theorem private_only {ws : List Word} {a : Word} (ha : a∈ws) {i : Nat}
    (h : (privateMask ws a).testBit i=true) :
    (sep a).testBit i=true ∧ ∀ b∈ws, b≠a → (sep b).testBit i=false := by
  simp only [privateMask,Nat.testBit_and,Nat.testBit_xor,Bool.and_eq_true] at h
  obtain ⟨bit,one⟩ := h
  have first := firstMask ws i a ha bit
  have no : (multiplicities ws).2.testBit i=false := by
    cases m : (multiplicities ws).2.testBit i <;> simp_all
  refine ⟨bit,?_⟩
  intro b hb diff
  cases d : (sep b).testBit i with
  | false => rfl
  | true => exact Bool.noConfusion (no.symm.trans (secondMask ws i diff hb ha d bit))

def wordGate : Kind→Word→Word→Word
  | .conj => meet
  | .disj => join
  | .leftOnly => skip
  | .rightOnly => fun a b => skip b a

def leftNeeds : Kind→Bool
  | .conj | .rightOnly => true
  | .disj | .leftOnly => false

theorem bit_rule (op : Kind) (a b : Word) (i : Nat) :
    (wordGate op a b).1.testBit i = applyKind op (a.1.testBit i) (b.1.testBit i) ∧
    (wordGate op a b).2.testBit i = applyKind op (a.2.testBit i) (b.2.testBit i) := by
  cases op <;> simp only [wordGate,meet,join,skip,applyKind,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor]
  all_goals
    cases a.1.testBit i <;> cases b.1.testBit i <;> cases a.2.testBit i <;> cases b.2.testBit i <;> decide

theorem masked_l (op : Kind) (a b u : Bool) (miss : u≠leftNeeds op) :
    applyKind op a u = applyKind op b u := by
  cases op <;> cases u <;> simp_all [leftNeeds,applyKind]

theorem needed_bit {ws out : List Word} {a b : Word} (ha : a∈ws) (hb : b∈ws) (ab : a≠b)
    (op : Kind) (same : cover out=cover ws)
    (others : ∀w∈out, w=wordGate op a b ∨ w∈ws ∧ w≠a)
    {i : Nat} (p : (privateMask ws a).testBit i=true) :
    b.1.testBit i = leftNeeds op := by
  obtain ⟨da,only⟩ := private_only ha p
  have db := only b hb ab.symm
  have beq : b.1.testBit i=b.2.testBit i := by
    simp only [sep,Nat.testBit_xor] at db
    cases hl : b.1.testBit i <;> cases hr : b.2.testBit i <;> simp_all
  have on := (covered_iff ws i).2 ⟨a,ha,da⟩
  rw [←same] at on
  obtain ⟨w,hw,good⟩ := (covered_iff out i).1 on
  rcases others w hw with e|⟨belongs,no⟩
  · subst w
    apply Classical.byContradiction
    intro neg
    obtain ⟨lo,hi⟩ := bit_rule op a b i
    have flat := masked_l op (a.1.testBit i) (a.2.testBit i) (b.1.testBit i) neg
    rw [←beq] at hi
    simp [sep,Nat.testBit_xor,lo,hi,flat] at good
  · exact Bool.noConfusion ((only w belongs no).symm.trans good)

end CoNatBench
namespace CoNatBench
open CoThetaFreeCore

def maskOK (word mask : Nat) (want : Bool) : Bool :=
  if want then (mask &&& word)==mask else (mask &&& word)==0

theorem mask_hit {ws out : List Word} {a b : Word} (ha : a∈ws) (hb : b∈ws) (ab : a≠b)
    (op : Kind) (same : cover out=cover ws)
    (others : ∀w∈out, w=wordGate op a b ∨ w∈ws ∧ w≠a) :
    maskOK b.1 (privateMask ws a) (leftNeeds op)=true := by
  have key := fun i => @needed_bit ws out a b ha hb ab op same others i
  cases d : leftNeeds op with
  | false =>
    simp only [maskOK,Bool.false_eq_true,↓reduceIte,beq_iff_eq]
    apply Nat.eq_of_testBit_eq
    intro i
    cases h : (privateMask ws a).testBit i with
    | false => simp [Nat.testBit_and,h]
    | true => simp [Nat.testBit_and,h,key i h,d]
  | true =>
    simp only [maskOK,↓reduceIte,beq_iff_eq]
    apply Nat.eq_of_testBit_eq
    intro i
    cases h : (privateMask ws a).testBit i with
    | false => simp [Nat.testBit_and,h]
    | true => simp [Nat.testBit_and,h,key i h,d]

def reflectOp : Kind→Kind
  | .conj => .conj
  | .disj => .disj
  | .leftOnly => .rightOnly
  | .rightOnly => .leftOnly

theorem gate_swap (op : Kind) (a b : Word) : wordGate (reflectOp op) b a=wordGate op a b := by
  cases op <;> simp [reflectOp,wordGate,meet,join,skip,Nat.and_comm,Nat.or_comm]

def restOf (ws : List Word) (a b : Word) := ws.filter (fun w => w != a && w != b)
def keepList (ka kb : Bool) (a b : Word) := (if ka then [a] else [])++(if kb then [b] else [])
def extension (ws : List Word) (a b : Word) (op : Kind) (ka kb : Bool) :=
  wordGate op a b::(keepList ka kb a b ++ restOf ws a b)

theorem rest_mem {ws : List Word} {a b w} : w∈restOf ws a b ↔ w∈ws ∧ w≠a ∧ w≠b := by
  simp [restOf]

theorem kept_mask_left {ws : List Word} {a b : Word} (op : Kind)
    (ha : a∈ws) (hb : b∈ws) (ab : a≠b) (kb : Bool)
    (full : cover (extension ws a b op false kb)=cover ws) :
    maskOK b.1 (privateMask ws a) (leftNeeds op)=true := by
  apply mask_hit ha hb ab op full
  intro w hw
  rcases List.mem_cons.mp hw with eq|ht
  · exact Or.inl eq
  · right
    rcases List.mem_append.mp ht with hk|hr
    · cases kb <;> simp [keepList] at hk
      exact hk ▸ And.intro hb ab.symm
    · have h := rest_mem.mp hr
      exact ⟨h.1,h.2.1⟩

theorem kept_mask_right {ws : List Word} {a b : Word} (op : Kind)
    (ha : a∈ws) (hb : b∈ws) (ab : a≠b) (ka : Bool)
    (full : cover (extension ws a b op ka false)=cover ws) :
    maskOK a.1 (privateMask ws b) (leftNeeds (reflectOp op))=true := by
  apply mask_hit hb ha ab.symm (reflectOp op) full
  intro w hw
  rcases List.mem_cons.mp hw with eq|ht
  · exact Or.inl (eq.trans (gate_swap op a b).symm)
  · right
    rcases List.mem_append.mp ht with hk|hr
    · cases ka <;> simp [keepList] at hk
      exact hk ▸ And.intro ha ab
    · have h := rest_mem.mp hr
      exact ⟨h.1,h.2.2⟩

end CoNatBench
namespace CoNatBench
open CoThetaFreeCore

def tryField (k : Nat) (next : List Word→Bool) (ws : List Word) (a b : Word×Nat) (op : Kind) : Bool :=
  let n := ws.length
  let half := n≤k+1
  let stay := n≤k
  let rest := restOf ws a.1 b.1
  let base := cover rest
  let oka := maskOK b.1.1 a.2 (leftNeeds op)
  let okb := maskOK a.1.1 b.2 (leftNeeds (reflectOp op))
  (stay || (half && (oka || okb)) || (oka && okb)) &&
    (let z := wordGate op a.1 b.1
     z != (0,0) && !(ws.contains z) &&
      ((oka && okb && (base ||| sep z)==all && next (z::rest)) ||
       (half && okb && next (z::a.1::rest)) ||
       (half && oka && next (z::b.1::rest)) ||
       (stay && next (z::a.1::b.1::rest))))

def pairTry (k : Nat) (next : List Word→Bool) (ws : List Word) (a b : Word×Nat) : Bool :=
  tryField k next ws a b .conj || tryField k next ws a b .disj ||
    tryField k next ws a b .leftOnly || tryField k next ws a b .rightOnly

theorem guarded_eq (k : Nat) (next : List Word→Bool) (ws : List Word) :
    guarded k next ws =
      if ws.length>k+2 then false else
        pairs (pairTry k next ws) (ws.map fun a => (a,privateMask ws a)) := rfl

theorem cover_cons (w : Word) (ws : List Word) : cover (w::ws)=sep w ||| cover ws := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [cover,foldBits,Nat.testBit_or]

theorem drop_len (ws : List Word) (d : Word) (nd : ws.Nodup) (hd : d∈ws) :
    (ws.filter (fun w => w != d)).length+1=ws.length := by
  induction ws with
  | nil => simp at hd
  | cons x xs ih =>
    obtain ⟨fresh,rest⟩ := List.nodup_cons.mp nd
    by_cases e : x=d
    · subst x
      have self : xs.filter (fun w => w != d)=xs := List.filter_eq_self.mpr (by
        intro v hv
        have neq : v≠d := fun eq => fresh (eq ▸ hv)
        simp [neq])
      simp [self]
    · have hit := (List.mem_cons.mp hd).resolve_left (Ne.symm e)
      have n := ih rest hit
      simp [e,n]

theorem rest_len (ws : List Word) (a b : Word) (nd : ws.Nodup) (ha : a∈ws) (hb : b∈ws) (ab : a≠b) :
    (restOf ws a b).length+2=ws.length := by
  let after := ws.filter (fun w => w != a)
  have inside : b∈after := by simp [after,hb,ab.symm]
  have n1 := drop_len ws a nd ha
  have n2 := drop_len after b (nd.filter _) inside
  have order : (after.filter (fun w => w != b))=restOf ws a b := by
    simp [after,restOf,List.filter_filter,Bool.and_comm]
  rw [order] at n2
  dsimp [after] at n2
  omega

theorem tryField_hit {k : Nat} {ws : List Word} {a b : Word} (op : Kind) (ka kb : Bool)
    (next : List Word→Bool) (nd : ws.Nodup) (ha : a∈ws) (hb : b∈ws) (ab : a≠b)
    (non : wordGate op a b≠(0,0)) (fresh : wordGate op a b∉ws)
    (wide : (extension ws a b op ka kb).length≤k+1) (old : cover ws=all)
    (new : cover (extension ws a b op ka kb)=all) (pass : next (extension ws a b op ka kb)=true) :
    tryField k next ws (a,privateMask ws a) (b,privateMask ws b) op=true := by
  have remaining := rest_len ws a b nd ha hb ab
  have same := new.trans old.symm
  cases ka <;> cases kb
  · have l := kept_mask_left op ha hb ab false same
    have r := kept_mask_right op ha hb ab false same
    have cc : cover (restOf ws a b) ||| sep (wordGate op a b)=all := by
      simpa [extension,keepList,cover_cons,Nat.or_comm] using new
    simp [extension,keepList] at pass
    simp [tryField,l,r,non,fresh,cc,pass]
  · have l := kept_mask_left op ha hb ab true same
    have width : ws.length≤k+1 := by simp [extension,keepList] at wide; omega
    simp [extension,keepList] at pass
    simp [tryField,l,width,non,fresh,pass]
  · have r := kept_mask_right op ha hb ab true same
    have width : ws.length≤k+1 := by simp [extension,keepList] at wide; omega
    simp [extension,keepList] at pass
    simp [tryField,r,width,non,fresh,pass]
  · have width : ws.length≤k := by simp [extension,keepList] at wide; omega
    simp [extension,keepList] at pass
    simp [tryField,width,non,fresh,pass]

end CoNatBench
namespace CoNatBench
open CoThetaFreeCore

theorem project_inj {a b : CoThetaBits.Wire} (h : project a=project b) : a=b := by
  apply Prod.ext <;> apply BitVec.eq_of_toNat_eq
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

@[simp] theorem project_eq {a b : CoThetaBits.Wire} : project a=project b ↔ a=b :=
  ⟨project_inj,congrArg project⟩

private theorem mask_sub {n} (a b : BitVec n) :
    (a &&& ~~~b)=a ^^^ (a &&& b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

private theorem mask_rev {n} (a b : BitVec n) :
    (~~~a &&& b)=b ^^^ (b &&& a) := by rw [BitVec.and_comm,mask_sub]

theorem project_gate (op : Kind) (a b : CoThetaBits.Wire) :
    project (CoThetaBits.gate op a b)=wordGate op (project a) (project b) := by
  cases op <;> simp only [project,CoThetaBits.gate,wordGate,meet,join,skip,mask_sub,mask_rev,
    BitVec.toNat_and,BitVec.toNat_or,BitVec.toNat_xor]

theorem project_cover (ws : List CoThetaBits.Wire) :
    cover (ws.map project)=(CoThetaBits.coverage ws).toNat := by
  induction ws with
  | nil => change 0=(0:CoThetaBits.Bits).toNat; simp
  | cons w ws ih => simp [cover_cons,project,sep,CoThetaBits.coverage,CoThetaBits.sep,ih]

theorem project_trim (xs : List CoThetaBits.Wire) (a b : CoThetaBits.Wire) :
    (CoThetaBits.trim a b xs).map project=restOf (xs.map project) (project a) (project b) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases e : x=a <;> by_cases h : x=b <;>
      simp [CoThetaBits.trim,restOf,e,h,project_eq] at * <;> exact ih

theorem project_edit (ws : List CoThetaBits.Wire) (a b : CoThetaBits.Wire) (op : Kind)
    (U : (CoThetaBits.Row→Bool)→Prop) :
    (CoThetaBits.gate op a b::(CoThetaBits.kept a b U++CoThetaBits.trim a b ws)).map project=
      extension (ws.map project) (project a) (project b) op
        (@decide _ (Classical.propDecidable (U (CoThetaBits.den a))))
        (@decide _ (Classical.propDecidable (U (CoThetaBits.den b)))) := by
  classical
  by_cases p : U (CoThetaBits.den a) <;> by_cases q : U (CoThetaBits.den b) <;>
    simp [CoThetaBits.kept,extension,keepList,p,q,project_gate,project_trim]

theorem pair_hit (k : Nat) (next : List Word→Bool) (ws : List Word) (a b : Word×Nat) (op : Kind)
    (h : tryField k next ws a b op=true) : pairTry k next ws a b=true := by
  cases op <;> simp [pairTry,h]

theorem pairs_hit {α} (test : α→α→Bool) {a b : α} {ws : List α}
    (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (go : test a b=true) (back : test b a=true) :
    pairs test ws=true := by
  classical
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    rw [pairs,Bool.or_eq_true]
    by_cases eq : a=w
    · subst w
      exact Or.inl (List.any_eq_true.mpr ⟨b,(List.mem_cons.mp hb).resolve_left ne.symm,go⟩)
    · by_cases e : b=w
      · subst w
        exact Or.inl (List.any_eq_true.mpr ⟨a,(List.mem_cons.mp ha).resolve_left ne,back⟩)
      · exact Or.inr (ih ((List.mem_cons.mp ha).resolve_left eq) ((List.mem_cons.mp hb).resolve_left e))

end CoNatBench
namespace CoNatBench
open CoThetaFreeCore
open CoThetaBits (Wire Row Rep den gate full)

private theorem project_nodup {xs : List Wire} (h : xs.Nodup) : (xs.map project).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨no,rest⟩ := List.nodup_cons.mp h
    simp only [List.map_cons,List.nodup_cons]
    refine ⟨?_,ih rest⟩
    intro h
    obtain ⟨b,hb,eq⟩ := List.mem_map.mp h
    exact no (project_inj eq ▸ hb)

private theorem seen_iff {S ws} (rep : Rep ws S) (a : Wire) : a∈ws ↔ S (den a) := by
  constructor
  · exact fun ha => (rep _).2 ⟨a,ha,rfl⟩
  · intro h
    obtain ⟨b,hb,eq⟩ := (rep _).1 h
    exact CoThetaBits.den_injective eq ▸ hb

private theorem direction_hit {m k : Nat} {ws : List Wire} {x y : Wire} {U}
    (op : Kind) (nd : ws.Nodup) (hx : x∈ws) (hy : y∈ws) (ne : x≠y)
    (non : gate op x y≠CoThetaBits.zero) (fresh : gate op x y∉ws)
    (rep : Rep ws (ins (den x) (ins (den y) U)))
    (remaining : Live (den CoThetaBits.target) m (ins (den (gate op x y)) U)) (enough : m≤k)
    (old : CoThetaBits.coverage ws=full)
    (recur : ∀ zs, zs.Nodup → Rep zs (ins (den (gate op x y)) U) →
      guardedSearch k (zs.map project)=true) :
    pairTry k (guardedSearch k) (ws.map project)
      (project x,privateMask (ws.map project) (project x))
      (project y,privateMask (ws.map project) (project y))=true := by
  classical
  let z := gate op x y
  let out := z::(CoThetaBits.kept x y U++CoThetaBits.trim x y ws)
  have ro : Rep out (ins (den z) U) := CoThetaBits.edit_rep rep
  have d : out.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,CoThetaBits.edit_distinct ne nd⟩
    intro hz
    exact fresh ((seen_iff rep z).2 (Or.inr (Or.inr ((CoThetaBits.edit_member rep).1 hz))))
  have nz : wordGate op (project x) (project y)≠(0,0) := by
    rw [←project_gate]
    intro eq
    apply non
    apply project_inj
    simpa [project,CoThetaBits.zero] using eq
  have nf : wordGate op (project x) (project y)∉ws.map project := by
    rw [←project_gate]
    intro v
    obtain ⟨w,hw,eq⟩ := List.mem_map.mp v
    exact fresh (project_inj eq ▸ hw)
  let ka := decide (U (den x))
  let kb := decide (U (den y))
  have em : out.map project=extension (ws.map project) (project x) (project y) op ka kb :=
    project_edit ws x y op U
  have width := CoThetaBits.state_width remaining d ro
  have cov := CoThetaBits.live_coverage out remaining (fun w h => (ro w).1 h)
  apply pair_hit k _ _ _ _ op
  apply tryField_hit op ka kb _ (project_nodup nd) (List.mem_map_of_mem hx)
    (List.mem_map_of_mem hy) (fun eq => ne (project_inj eq)) nz nf
  · rw [←em,List.length_map]
    omega
  · rw [project_cover,old]
    rfl
  · rw [←em,project_cover,cov]
    rfl
  · rw [←em]
    exact recur out d ro

theorem guarded_complete {m S} (run : Live (den CoThetaBits.target) m S) :
    ∀ fuel, m≤fuel → ∀ ws, ws.Nodup → Rep ws S → guardedSearch fuel (ws.map project)=true := by
  classical
  induction run with
  | stop =>
    intro fuel _ ws _ rep
    have hit := List.mem_map_of_mem (f:=project) ((seen_iff rep CoThetaBits.target).2 rfl)
    cases fuel <;> simp [guardedSearch,target,hit]
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
      have e : den z=(fun i => applyKind kind (den x i) (den y i)) := CoThetaBits.den_gate _ _ _
      have dist : x≠y := fun eq => ab (congrArg den eq)
      have rt : Live (den CoThetaBits.target) m (ins (den z) U) := by rw [e]; exact tail
      have ng : den CoThetaBits.target≠absentBit := by
        intro h
        have bad := congrFun h (true,0)
        simp [CoThetaBits.den_target,absentBit] at bad
      have non : z≠CoThetaBits.zero := by
        intro eq
        have eq2 := (congrArg den eq).trans CoThetaBits.den_zero
        exact rt.excludes_zero ng (Or.inl eq2.symm)
      have nf : z∉ws := fun h => fresh (e ▸ (seen_iff rep z).1 h)
      have current := Live.step kind ab ha hb fresh tail
      have fullWs := CoThetaBits.live_coverage ws current (fun w h => (rep w).1 h)
      have boundK : m≤k := by omega
      have recurse : ∀ ys, ys.Nodup → Rep ys (ins (den z) U) → guardedSearch k (ys.map project)=true := by
        intro ys h r
        rw [e] at r
        exact ih k boundK ys h r
      have forward := direction_hit kind nd hx hy dist non nf rep rt boundK fullWs recurse
      have swapped : gate (reflectOp kind) y x=z := by
        apply project_inj
        simp [z,project_gate,gate_swap]
      have revRep : Rep ws (ins (den y) (ins (den x) U)) := by
        intro w
        simpa [ins,or_left_comm] using rep w
      have reverse : pairTry k (guardedSearch k) (ws.map project)
          (project y,privateMask (ws.map project) (project y)) (project x,privateMask (ws.map project) (project x))=true := by
        apply direction_hit (reflectOp kind) nd hy hx dist.symm <;> try rw [swapped]
        · exact non
        · exact nf
        · exact revRep
        · exact rt
        · exact boundK
        · exact fullWs
        · exact recurse
      let natWs := ws.map project
      let points := natWs.map (fun v => (v,privateMask natWs v))
      have one : (project x,privateMask natWs (project x))∈points :=
        List.mem_map_of_mem (List.mem_map_of_mem hx)
      have two : (project y,privateMask natWs (project y))∈points :=
        List.mem_map_of_mem (List.mem_map_of_mem hy)
      have distinct : (project x,privateMask natWs (project x))≠(project y,privateMask natWs (project y)) :=
        fun eq => dist (project_inj (congrArg Prod.fst eq))
      have pass := pairs_hit (pairTry k (guardedSearch k) natWs) one two distinct forward reverse
      have size := CoThetaBits.state_width current nd rep
      have limit : ¬(ws.map project).length>k+2 := by simp only [List.length_map]; omega
      rw [guardedSearch,Bool.or_eq_true]
      right
      rw [guarded_eq,if_neg limit]
      exact pass

end CoNatBench
namespace CoThetaSix
open CoThetaBits
open CoNatBench
def cycle : List CoThetaBits.Wire := [(0x401f80fff40701fff,0x400f006ba486086a6),
(0x81e3f3070807ffe00,0x80a1a10608232d414),
(0x3067c0c180ff801fff,0x3027004100a3001958),
(0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc07800fe00ffffe000,0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc05000ac005c4d0020),
(0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000ffff00000000,0x590000f94410060040),
(0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000,0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa675a4000820080180)]
theorem cycle_small : CoNatBench.guardedSearch 7 (cycle.map CoNatBench.project)=false := by decide +kernel
def cyclePrivate : List Nat := [3, 16, 1, 14, 33, 49]
def pendant : List CoThetaBits.Wire := [(0x118fc1cffbf0601ff,0x108780c5d1e420896),
(0x2071fe33847fffe00,0x2020d213003924c04),
(0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcc19e003c07807ffff,0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcc118002806005b168),
(0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01e007c007ff80000,0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff05c00580074602030),
(0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0007fff80000000,0x56400073a20080c040),
(0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800000000000,0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa99dd2000400010180)]
theorem pendant_small : CoNatBench.guardedSearch 7 (pendant.map CoNatBench.project)=false := by decide +kernel
def pendantPrivate : List Nat := [3, 12, 1, 20, 32, 48]
end CoThetaSix
namespace CoNatBench
open CoThetaFreeCore
open CoThetaBits (Wire Row Rep den)

def essentialBasis (roots : List Wire) : Prop :=
  ∀ w∈roots, ∃ i : Fin CoThetaBits.Width, ∀ v∈roots,
    den v (true,i)≠den v (false,i) → v=w

theorem generic_rep {m S} {roots : List Wire} (live : Live (den CoThetaBits.target) m S)
    (onlyRaw : ∀ f, S f → f=absentBit ∨ ∃ w∈roots, den w=f)
    (required : essentialBasis roots) : Rep roots S := by
  have ng : den CoThetaBits.target≠absentBit := by
    intro e
    have no := congrFun e (true,0)
    simp [CoThetaBits.den_target,absentBit] at no
  intro f
  constructor
  · intro hf
    rcases onlyRaw f hf with z|h
    · exact (live.excludes_zero ng (z ▸ hf)).elim
    · exact h
  · rintro ⟨w,hw,eq⟩
    obtain ⟨i,key⟩ := required w hw
    have d : den CoThetaBits.target (true,i)≠den CoThetaBits.target (false,i) := by simp [CoThetaBits.den_target]
    obtain ⟨v,hv,diff⟩ := live.separates (true,i) (false,i) d
    rcases onlyRaw v hv with z|⟨u,hu,e⟩
    · subst v
      exact (diff rfl).elim
    · subst v
      obtain rfl := key u hu diff
      exact eq ▸ hv

theorem table_bound {roots : List Wire} (required : essentialBasis roots)
    (nd : roots.Nodup) {n ws} (run : Free (absentBit::roots.map den) n ws)
    (goal : den CoThetaBits.target∈ws) {cap : Nat} (cert : guardedSearch cap (roots.map project)=false) : cap<n := by
  obtain ⟨k,S,le,live,sub⟩ := rewind run List.mem_cons_self
    (Live.stop (goal:=den CoThetaBits.target)) (fun w e => e.symm ▸ goal)
  apply Classical.byContradiction
  intro bad
  apply Bool.false_ne_true
  rw [←cert]
  apply guarded_complete live cap (by omega) roots nd
  apply generic_rep live _ required
  intro f h
  rcases List.mem_cons.mp (sub f h) with z|raw
  · exact Or.inl z
  · exact Or.inr (List.mem_map.mp raw)

end CoNatBench

namespace CoThetaSix
open CoThetaFreeCore
open CoThetaBits (Wire Row den)

def basisAt (ws : List Wire) (ids : List Nat) : Bool :=
  (List.range ws.length).all fun a =>
    let i := (ids.getD a 0) % CoThetaBits.Width
    ws.all fun v =>
      let want := ws.getD a CoThetaBits.zero
      (den v (true,⟨i,Nat.mod_lt _ (by decide)⟩) == den v (false,⟨i,Nat.mod_lt _ (by decide)⟩)) || v==want

theorem basisAt_sound (ws : List Wire) (ids : List Nat) (cert : basisAt ws ids=true) :
    CoNatBench.essentialBasis ws := by
  intro w hw
  obtain ⟨k,hk,eq⟩ := List.mem_iff_getElem.mp hw
  let i := (ids.getD k 0) % CoThetaBits.Width
  refine ⟨⟨i,Nat.mod_lt _ (by decide)⟩,?_⟩
  intro v hv ne
  have each := List.all_eq_true.mp cert k (List.mem_range.mpr hk)
  have hit := List.all_eq_true.mp each v hv
  simp only [Bool.or_eq_true,beq_iff_eq] at hit
  have vwant := hit.resolve_left ne
  simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,eq] using vwant

theorem cycle_basis : CoNatBench.essentialBasis cycle := basisAt_sound cycle cyclePrivate (by decide +kernel)
theorem pendant_basis : CoNatBench.essentialBasis pendant := basisAt_sound pendant pendantPrivate (by decide +kernel)
theorem cycle_nd : cycle.Nodup := by decide +kernel
theorem pendant_nd : pendant.Nodup := by decide +kernel

end CoThetaSix
namespace CoThetaSix
open CoThetaFreeCore
open CoThetaBits (Wire Row den gate)
open CoThetaNine (SmallInput raw7 ans7 vertices7 pack unpack numeric_goal)

def rootsFor (gone : Fin 7) := if gone=2 then cycle else pendant

def indexAt (gone vertex : Fin 7) : Option Nat :=
  match gone.val,vertex.val with
  | 2,0 => some 0
  | 2,1 => some 1
  | 2,3 => some 2
  | 2,4 => some 3
  | 2,5 => some 4
  | 2,6 => some 5
  | 3,0 => some 0
  | 3,1 => some 1
  | 3,2 => some 2
  | 3,4 => some 3
  | 3,5 => some 4
  | 3,6 => some 5
  | 4,1 => some 0
  | 4,0 => some 1
  | 4,2 => some 2
  | 4,3 => some 3
  | 4,6 => some 4
  | 4,5 => some 5
  | 5,0 => some 0
  | 5,1 => some 1
  | 5,2 => some 2
  | 5,6 => some 3
  | 5,3 => some 4
  | 5,4 => some 5
  | 6,1 => some 0
  | 6,0 => some 1
  | 6,2 => some 2
  | 6,5 => some 3
  | 6,4 => some 4
  | 6,3 => some 5
  | _,_ => none

def minorCol (gone vertex : Fin 7) : Wire :=
  match indexAt gone vertex with
  | none => CoThetaBits.zero
  | some n => (rootsFor gone).getD n CoThetaBits.zero

def minorLift (g : Fin 7) (r : Row) : SmallInput := pack (fun j => den (minorCol g j) r)
def minorGraph (g : Fin 7) : Wire :=
  gate .disj (gate .disj (gate .disj (gate .disj (gate .disj (gate .disj (gate .disj
    (gate .conj (minorCol g 0) (minorCol g 2)) (gate .conj (minorCol g 1) (minorCol g 2)))
    (gate .conj (minorCol g 0) (minorCol g 3))) (gate .conj (minorCol g 3) (minorCol g 4)))
    (gate .conj (minorCol g 1) (minorCol g 4))) (gate .conj (minorCol g 0) (minorCol g 5)))
    (gate .conj (minorCol g 5) (minorCol g 6))) (gate .conj (minorCol g 1) (minorCol g 6))

theorem minor_table : ∀ g : Fin 7, 2≤g.val → minorGraph g=CoThetaBits.target ∧
    minorCol g g=CoThetaBits.zero := by decide +kernel

theorem minor_input (g j : Fin 7) :
    restrict (minorLift g) (raw7 j)=den (minorCol g j) :=
  funext (fun r => unpack (fun v => den (minorCol g v) r) j)

theorem minor_goal {g : Fin 7} (small : 2≤g.val) :
    restrict (minorLift g) ans7=den CoThetaBits.target := by
  have graph := congrArg den (minor_table g small).1
  funext r
  change ans7 (minorLift g r)=_
  rw [numeric_goal]
  have values : (fun j => raw7 j (minorLift g r))=(fun j => den (minorCol g j) r) :=
    funext (fun j => congrFun (minor_input g j) r)
  rw [values]
  have equality := congrFun graph r
  simp only [minorGraph,CoThetaBits.den_gate,applyKind] at equality
  exact equality

theorem minor_off {g : Fin 7} (small : 2≤g.val) :
    restrict (minorLift g) (raw7 g)=absentBit :=
  (minor_input g g).trans ((congrArg den (minor_table g small).2).trans CoThetaBits.den_zero)

theorem minor_known (g : Fin 7) : ∀ w∈vertices7,
    restrict (minorLift g) w∈absentBit::(rootsFor g).map den := by
  intro w hw
  rcases List.mem_cons.mp hw with z|r
  · subst w
    exact List.mem_cons_self
  · obtain ⟨j,e⟩ := List.mem_ofFn.mp r
    subst w
    rw [minor_input]
    cases h : indexAt g j with
    | none => simp [minorCol,h,CoThetaBits.den_zero]
    | some n =>
      cases hn : (rootsFor g)[n]? with
      | none => simp [minorCol,h,List.getD_eq_getElem?_getD,hn,CoThetaBits.den_zero]
      | some v =>
        have inList := List.mem_map_of_mem (f:=den) (List.mem_of_getElem? hn)
        simp [minorCol,h,List.getD_eq_getElem?_getD,hn,inList]

theorem minor_lower {g : Fin 7} (small : 2≤g.val) {gs : List (TraceGate SmallInput)}
    (ok : sufficient vertices7 ans7 gs) : 8≤remaining (minorLift g) gs := by
  let roots := rootsFor g
  obtain ⟨ws,run,all⟩ := restrict_trace (minorLift g) gs ok.1
    (Free.start (raw:=absentBit::roots.map den)) List.mem_cons_self (minor_known g)
  have h := all ans7 ok.2
  rw [minor_goal small] at h
  have yes : 7<0+remaining (minorLift g) gs := by
    by_cases e : g=2
    · exact CoNatBench.table_bound (roots:=roots) (by simpa [roots,rootsFor,e] using cycle_basis)
        (by simpa [roots,rootsFor,e] using cycle_nd) run h (by simpa [roots,rootsFor,e] using cycle_small)
    · exact CoNatBench.table_bound (roots:=roots) (by simpa [roots,rootsFor,e] using pendant_basis)
        (by simpa [roots,rootsFor,e] using pendant_nd) run h (by simpa [roots,rootsFor,e] using pendant_small)
  omega

end CoThetaSix
namespace CoThetaFreeCore

noncomputable local instance {ρ : Type} : DecidableEq (TraceGate ρ) := Classical.decEq _

noncomputable def readerSet {ρ : Type} (gs : List (TraceGate ρ)) (p : ρ → Bool) :
    Finset (TraceGate ρ) := by classical exact gs.toFinset.filter (fun g => reads g p)

theorem mem_readerSet {ρ : Type} {gs : List (TraceGate ρ)} {p : ρ → Bool}
    {g : TraceGate ρ} : g ∈ readerSet gs p ↔ g ∈ gs ∧ reads g p := by
  classical
  simp [readerSet]


theorem three_readers_separate_head {α : Type} [DecidableEq α] (P Q : Finset α)
    (twoP : 2 ≤ P.card) (someQ : Q.Nonempty) (head : ∃ g ∈ P, g ∉ Q)
    (shared : ∀ g ∈ P, g ∈ Q → 2 ≤ Q.card) : 3 ≤ (P ∪ Q).card := by
  classical
  by_cases both : ∃ g ∈ P, g ∈ Q
  · obtain ⟨g,hg,hq⟩ := both
    obtain ⟨h,hp,hn⟩ := head
    have sub : insert h Q ⊆ P ∪ Q := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact Finset.mem_union_left _ hp
      · exact Finset.mem_union_right _ hv
    have hc := Finset.card_le_card sub
    rw [Finset.card_insert_of_notMem hn] at hc
    have low := shared g hg hq
    omega
  · obtain ⟨q,hq⟩ := someQ
    have out : q ∉ P := fun hp => both ⟨q,hp,hq⟩
    have sub : insert q P ⊆ P ∪ Q := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact Finset.mem_union_right _ hq
      · exact Finset.mem_union_left _ hv
    have hc := Finset.card_le_card sub
    rw [Finset.card_insert_of_notMem out] at hc
    omega


inductive UsePath {ρ : Type} (gs : List (TraceGate ρ)) :
    (ρ → Bool) → (ρ → Bool) → Prop
  | stop {w} : UsePath gs w w
  | through {w out} (g : TraceGate ρ) (mem : g ∈ gs) (input : reads g w)
      (rest : UsePath gs g.value out) : UsePath gs w out

private theorem two_reads_zero {ρ σ : Type} (lift : σ → ρ)
    {g : TraceGate ρ} {w p : ρ → Bool} (ne : w ≠ p) (hw : reads g w) (hp : reads g p)
    (zw : restrict lift w = absentBit) (zp : restrict lift p = absentBit) :
    restrict lift g.value = absentBit := by
  apply two_zero_propagate
  · rcases hw with h|h <;> rcases hp with h'|h'
    · exact (ne (h.symm.trans h')).elim
    · exact (congrArg (restrict lift) h).trans zw
    · exact (congrArg (restrict lift) h').trans zp
    · exact (ne (h.symm.trans h')).elim
  · rcases hw with h|h <;> rcases hp with h'|h'
    · exact (ne (h.symm.trans h')).elim
    · exact (congrArg (restrict lift) h').trans zp
    · exact (congrArg (restrict lift) h).trans zw
    · exact (ne (h.symm.trans h')).elim


theorem extra_loss_on_path {ρ σ : Type} (lift : σ → ρ) {gs : List (TraceGate ρ)}
    {p q z out : ρ → Bool} (zp : restrict lift p = absentBit) (zq : restrict lift q = absentBit)
    (aliasFree : ∀ g ∈ gs, g.value ≠ p ∧ g.value ≠ q)
    (path : UsePath gs z out) (zz : restrict lift z = absentBit)
    (distinct : z ≠ p ∧ z ≠ q) (ends : restrict lift out ≠ absentBit) :
    ∃ g ∈ gs, ¬reads g p ∧ ¬reads g q ∧ disappears lift g := by
  induction path with
  | stop => exact (ends zz).elim
  | @through w out g hg hw more ih =>
    by_cases hp : reads g p
    · exact ih (two_reads_zero lift distinct.1 hw hp zz zp) (aliasFree g hg) ends
    by_cases hq : reads g q
    · exact ih (two_reads_zero lift distinct.2 hw hq zz zq) (aliasFree g hg) ends
    exact ⟨g,hg,hp,hq,reading_zero_disappears lift zz hw⟩

private noncomputable def lostList {ρ σ : Type} (lift : σ → ρ) (gs : List (TraceGate ρ)) :
    List (TraceGate ρ) := by classical exact gs.filter (fun g => decide (disappears lift g))

private theorem lost_length {ρ σ : Type} (lift : σ → ρ) (gs : List (TraceGate ρ)) :
    (lostList lift gs).length = saved lift gs := by
  classical
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    by_cases h : disappears lift g <;> simp [lostList,saved,h,lostList] at ih ⊢ <;> omega

theorem four_saved_raw_head {ρ σ : Type} (lift : σ → ρ) (gs : List (TraceGate ρ))
    (p q : ρ → Bool) (zp : restrict lift p = absentBit) (zq : restrict lift q = absentBit)
    (three : 3 ≤ (readerSet gs p ∪ readerSet gs q).card)
    (extra : ∃ g ∈ gs, ¬reads g p ∧ ¬reads g q ∧ disappears lift g) :
    4 ≤ saved lift gs := by
  classical
  obtain ⟨g,hg,hp,hq,hd⟩ := extra
  let A := readerSet gs p ∪ readerSet gs q
  have hout : g ∉ A := by
    intro h
    rcases Finset.mem_union.mp h with h|h
    · exact hp (mem_readerSet.mp h).2
    · exact hq (mem_readerSet.mp h).2
  have sub : insert g A ⊆ (lostList lift gs).toFinset := by
    intro v hv
    have hv' : v∈gs ∧ disappears lift v := by
      rcases Finset.mem_insert.mp hv with rfl|hv
      · exact ⟨hg,hd⟩
      · rcases Finset.mem_union.mp hv with h|h
        · obtain ⟨hm,hr⟩ := mem_readerSet.mp h
          exact ⟨hm,reading_zero_disappears lift zp hr⟩
        · obtain ⟨hm,hr⟩ := mem_readerSet.mp h
          exact ⟨hm,reading_zero_disappears lift zq hr⟩
    simpa [lostList] using hv'
  have bound := (Finset.card_le_card sub).trans (List.toFinset_card_le _)
  rw [Finset.card_insert_of_notMem hout,lost_length] at bound
  change 3 ≤ A.card at three
  omega

end CoThetaFreeCore
namespace CoThetaFreeCore

theorem UsePath.trans {ρ : Type} {chain : List (TraceGate ρ)} {a b c : ρ → Bool}
    (first : UsePath chain a b) (last : UsePath chain b c) : UsePath chain a c := by
  induction first with
  | stop => exact last
  | through g hg hr _ ih => exact .through g hg hr (ih last)


theorem omit_path_scan {ρ : Type} (chain : List (TraceGate ρ)) (z : ρ → Bool)
    (gs : List (TraceGate ρ)) (sub : ∀ g∈gs, g∈chain)
    {raw start pool : List (ρ → Bool)} {b : Nat}
    (reg : registered start gs) (pre : Free raw b pool)
    (known : ∀ w∈start, ¬UsePath chain z w → w∈pool) :
    ∃ j ys, j ≤ b+gs.length ∧ Free raw j ys ∧
      ∀ w∈traceWires start gs, ¬UsePath chain z w → w∈ys := by
  induction gs generalizing start pool b with
  | nil => exact ⟨b,pool,by simp,pre,known⟩
  | cons g gs ih =>
    obtain ⟨hl,hr,rest⟩ := reg
    have hg := sub g List.mem_cons_self
    have tail (v) (hv : v∈gs) := sub v (List.mem_cons_of_mem _ hv)
    by_cases path : UsePath chain z g.value
    · have carry : ∀ w∈g.value::start, ¬UsePath chain z w → w∈pool := by
        intro w hw hn
        rcases List.mem_cons.mp hw with rfl|hw
        · exact (hn path).elim
        · exact known _ hw hn
      obtain ⟨j,ys,hj,run,avail⟩ := ih tail rest pre carry
      exact ⟨j,ys,by simp; omega,run,avail⟩
    · have pl : ¬UsePath chain z g.left := fun p =>
        path (p.trans (.through g hg (Or.inl rfl) .stop))
      have pr : ¬UsePath chain z g.right := fun p =>
        path (p.trans (.through g hg (Or.inr rfl) .stop))
      have next : Free raw (b+1) (g.value::pool) :=
        .binary pre g.kind (known _ hl pl) (known _ hr pr)
      have carry : ∀ w∈g.value::start, ¬UsePath chain z w → w∈g.value::pool := by
        intro w hw hn
        rcases List.mem_cons.mp hw with rfl|hw
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (known _ hw hn)
      obtain ⟨j,ys,hj,run,avail⟩ := ih tail rest next carry
      exact ⟨j,ys,by simp; omega,run,avail⟩

theorem omit_dead_head {ρ : Type} (raw : List (ρ → Bool))
    (gs : List (TraceGate ρ)) (z target : ρ → Bool)
    (reg : registered (z::raw) gs) (out : target∈traceWires (z::raw) gs)
    (dead : ¬UsePath gs z target) :
    ∃ j ys, j ≤ gs.length ∧ Free raw j ys ∧ target∈ys := by
  have known (w) (hw : w∈z::raw) (hn : ¬UsePath gs z w) : w∈raw := by
    rcases List.mem_cons.mp hw with rfl|hw
    · exact (hn .stop).elim
    · exact hw
  obtain ⟨j,ys,hj,run,avail⟩ := omit_path_scan gs z gs (fun _ h => h) reg (Free.start (raw:=raw)) known
  exact ⟨j,ys,by simpa using hj,run,avail _ out dead⟩

end CoThetaFreeCore

namespace CoThetaFreeCore

noncomputable local instance {ρ : Type} : DecidableEq (TraceGate ρ) := Classical.decEq _

private theorem masked_setting {ρ : Type} (g : TraceGate ρ) (p : ρ → Bool) (hp : reads g p) :
    ∃ b : Bool, ∀ r s, p r=b → p s=b → g.value r = g.value s := by
  obtain ⟨k,l,r⟩ := g
  rcases hp with h|h
  · change l=p at h
    subst l
    have valid : ∀ k : Kind, ∃ b : Bool, ∀ a c : Bool, applyKind k b a = applyKind k b c := by
      intro j
      cases j <;> decide
    obtain ⟨b,f⟩ := valid k
    exact ⟨b,fun x y hx hy => by simp only [TraceGate.value,hx,hy]; exact f _ _⟩
  · change r=p at h
    subst r
    have valid : ∀ k : Kind, ∃ b : Bool, ∀ a c : Bool, applyKind k a b = applyKind k c b := by
      intro j
      cases j <;> decide
    obtain ⟨b,f⟩ := valid k
    exact ⟨b,fun x y hx hy => by simp only [TraceGate.value,hx,hy]; exact f _ _⟩


theorem nonedge_head_dichotomy {ρ σ : Type} (lift : σ → ρ)
    (raw : List (ρ → Bool)) (head : TraceGate ρ) (gs : List (TraceGate ρ))
    (p q out : ρ → Bool)
    (reg : registered raw (head::gs)) (solves : out∈traceWires raw (head::gs))
    (hrp : reads head p) (hrq : ¬reads head q)
    (outp : out≠p) (outq : out≠q)
    (pTest : ∃ r s, agreeOutside (·=p) r s raw ∧ out r≠out s ∧ head.value r=head.value s)
    (qTest : ∀ b : Bool, ∃ r s, agreeOutside (·=q) r s raw ∧ out r≠out s ∧ p r=b ∧ p s=b)
    (zp : restrict lift p=absentBit) (zq : restrict lift q=absentBit)
    (zh : restrict lift head.value=absentBit) (endNZ : restrict lift out≠absentBit)
    (headNew : head.value≠p ∧ head.value≠q)
    (fresh : ∀ g∈gs, g.value≠p ∧ g.value≠q) :
    (∃ j ys, j ≤ gs.length ∧ Free raw j ys ∧ out∈ys) ∨ 4 ≤ saved lift (head::gs) := by
  classical
  by_cases alive : UsePath gs head.value out
  case neg =>
    exact Or.inl (omit_dead_head raw gs head.value out reg.2.2 solves alive)
  case pos =>
    right
    apply four_saved_raw_head lift (head::gs) p q zp zq
    · apply three_readers_separate_head
      · obtain ⟨r,s,hs,hd,hm⟩ := pTest
        obtain ⟨g,hg,hp,ne⟩ := second_reader p r s head reg hs solves outp hd hm
        apply Finset.one_lt_card.mpr
        exact ⟨g,mem_readerSet.mpr ⟨hg,hp⟩,head,mem_readerSet.mpr ⟨List.mem_cons_self,hrp⟩,ne⟩
      · obtain ⟨r,s,hs,hd,_,_⟩ := qTest false
        obtain ⟨g,hg,read,_⟩ := reader_witness (·=q) r s reg hs solves outq hd
        exact ⟨g,mem_readerSet.mpr ⟨hg,read⟩⟩
      · exact ⟨head,mem_readerSet.mpr ⟨List.mem_cons_self,hrp⟩,fun h => hrq (mem_readerSet.mp h).2⟩
      · intro g hgP hgQ
        obtain ⟨b,hm⟩ := masked_setting g p (mem_readerSet.mp hgP).2
        obtain ⟨r,s,hs,hd,hpR,hpS⟩ := qTest b
        obtain ⟨other,hOther,readsQ,ne⟩ := second_reader q r s g reg hs solves outq hd (hm r s hpR hpS)
        apply Finset.one_lt_card.mpr
        exact ⟨other,mem_readerSet.mpr ⟨hOther,readsQ⟩,g,hgQ,ne⟩
    · obtain ⟨g,hg,hp,hq,hd⟩ := extra_loss_on_path lift zp zq fresh alive zh headNew endNZ
      exact ⟨g,List.mem_cons_of_mem _ hg,hp,hq,hd⟩

end CoThetaFreeCore
namespace CoThetaSeven
open CoThetaFreeCore
open CoThetaNine (SmallInput raw7 ans7 vertices7 pack unpack)
open CoThetaSix (minorLift minor_off minor_goal minor_lower)

def smallRow (n : Nat) : SmallInput := ⟨n % 128,Nat.mod_lt _ (by decide)⟩
def sensSeeds : List Nat :=
  [0, 0, 4, 10, 8, 4, 4, 8, 4, 20, 4, 32, 4, 68, 4, 17, 0, 0, 16, 4, 4, 12, 4, 16, 4, 36, 4, 64, 2, 1, 1, 2, 0, 0, 1, 10, 1, 17, 1, 34, 1, 65, 16, 1, 1, 3, 1, 20, 0, 0, 1, 16, 1, 48, 1, 65, 2, 3, 8, 2, 2, 12, 2, 8, 0, 0, 2, 34, 2, 72, 64, 1, 1, 3, 1, 68, 1, 72, 1, 17, 0, 0, 1, 64, 2, 3, 32, 2, 2, 36, 2, 10, 2, 48, 2, 32, 0, 0]

def loRow (x y : Fin 7) (b : Bool) := smallRow (sensSeeds.getD (2*(7*x.val+y.val)+b.toNat) 0)
def hiRow (x y : Fin 7) (b : Bool) := smallRow ((loRow x y b).val ||| (1 <<< x.val))
theorem seven_sensitivity : ∀ (x y : Fin 7), x≠y → ∀ b : Bool,
    raw7 x (loRow x y b)=false ∧ raw7 x (hiRow x y b)=true ∧
    raw7 y (loRow x y b)=b ∧ raw7 y (hiRow x y b)=b ∧
    ans7 (loRow x y b)≠ans7 (hiRow x y b) ∧
    ∀ z : Fin 7, z≠x → raw7 z (loRow x y b)=raw7 z (hiRow x y b) := by decide +kernel

theorem seven_diff : ∀ (x y : Fin 7), x≠y → ∃ r : SmallInput, raw7 x r≠raw7 y r := by
  have table : ∀ p q : Fin 7, p≠q → raw7 p (smallRow (1 <<< p.val))≠raw7 q (smallRow (1 <<< p.val)) := by decide +kernel
  exact fun p q pq => ⟨_,table p q pq⟩
theorem seven_not_raw : ∀ x : Fin 7, ∃ r : SmallInput, ans7 r≠raw7 x r := by
  have table : ∀ p : Fin 7, ans7 (smallRow (1 <<< p.val))≠raw7 p (smallRow (1 <<< p.val)) := by decide +kernel
  exact fun p => ⟨_,table p⟩

theorem raw_mem (x : Fin 7) : raw7 x∈vertices7 := List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨x,rfl⟩)

theorem read_twice (x y : Fin 7) (xy : x≠y) (g : TraceGate SmallInput)
    (gx : reads g (raw7 x)) (gy : reads g (raw7 y)) {gs : List (TraceGate SmallInput)}
    (ok : sufficient vertices7 ans7 gs) : ∃ t∈gs, reads t (raw7 x) ∧ t≠g := by
  obtain ⟨r,ne⟩ := seven_diff x y xy
  have diff : raw7 x≠raw7 y := fun h => ne (congrFun h r)
  obtain ⟨sw,code⟩ := joint_reader_code _ _ diff g gx gy
  obtain ⟨b,mask⟩ := CoThetaNine.masks_some_value g.kind sw
  obtain ⟨lx,hx,ly,hy,out,fixed⟩ := seven_sensitivity x y xy b
  obtain ⟨r,notSame⟩ := seven_not_raw x
  apply second_reader (raw7 x) (loRow x y b) (hiRow x y b) g ok.1 _ ok.2
    (fun eq => notSame (congrFun eq r)) out
  · simpa only [code,lx,hx,ly,hy] using mask false true
  · intro w hw no
    rcases List.mem_cons.mp hw with e|h
    · subst w
      rfl
    · obtain ⟨i,e⟩ := List.mem_ofFn.mp h
      subst w
      exact fixed i (fun e => no (congrArg raw7 e))

theorem three_losses {ρ σ : Type} (lift : σ→ρ) (gs : List (TraceGate ρ)) {a b c : TraceGate ρ}
    (ha : a∈gs) (hb : b∈gs) (hc : c∈gs) (ab : a≠b) (ac : a≠c) (bc : b≠c)
    (da : disappears lift a) (db : disappears lift b) (dc : disappears lift c) :
    3≤saved lift gs := by
  classical
  have nd : [a,b,c].Nodup := by simp [ab,ac,bc]
  rw [saved_eq_length]
  apply length_of_cover [a,b,c] _ nd
  intro w h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with e|e|e <;> subst w <;> simp [vanishing,ha,hb,hc,da,db,dc]

theorem absorbing_head {g : TraceGate SmallInput} {gs : List (TraceGate SmallInput)}
    (ok : sufficient vertices7 ans7 (g::gs)) (fresh : freshTrace vertices7 (g::gs))
    (budget : (g::gs).length≤10) {x y : Fin 7} (xy : x≠y)
    (rx : reads g (raw7 x)) (ry : reads g (raw7 y)) (nonhub : 2≤x.val)
    (zero : restrict (minorLift x) g.value=absentBit) :
    ∃ n ws, n≤gs.length ∧ Free vertices7 n ws ∧ ans7∈ws := by
  classical
  by_cases path : UsePath gs g.value ans7
  · exfalso
    have off := minor_off nonhub
    have fin : restrict (minorLift x) ans7≠absentBit := by
      rw [minor_goal nonhub]
      intro e
      have no := congrFun e (true,0)
      simp [CoThetaBits.den_target,absentBit] at no
    have distinct {t : TraceGate SmallInput} (ht : t∈g::gs) : t.value≠raw7 x :=
      fun e => fresh_outputs fresh _ ht (e ▸ raw_mem x)
    have headNe := distinct (List.mem_cons_self (a:=g) (l:=gs))
    obtain ⟨b,hb,rb,bg⟩ := read_twice x y xy g rx ry ok
    obtain ⟨c,hc,nr,_,gone⟩ := extra_loss_on_path (minorLift x) off off
      (fun t ht => ⟨distinct (List.mem_cons_of_mem _ ht),distinct (List.mem_cons_of_mem _ ht)⟩)
      path zero ⟨headNe,headNe⟩ fin
    have gain := three_losses (minorLift x) (g::gs) List.mem_cons_self hb
      (List.mem_cons_of_mem _ hc) (Ne.symm bg) (fun e => nr (e ▸ rx)) (fun e => nr (e ▸ rb))
      (reading_zero_disappears _ off rx) (reading_zero_disappears _ off rb) gone
    have lo := minor_lower nonhub ok
    have tot := accounted (minorLift x) (g::gs)
    omega
  · exact omit_dead_head vertices7 gs g.value ans7 ok.1.2.2 ok.2 path

end CoThetaSeven
namespace CoThetaSeven
open CoThetaFreeCore
open CoThetaNine (SmallInput raw7 ans7 vertices7 pack unpack)
open CoThetaSix (minorLift minor_off)
def opIndex : Kind→Nat
  | .conj => 0 | .disj => 1 | .leftOnly => 2 | .rightOnly => 3
def opAt (n : Nat) : Kind := match n with
  | 0 => .conj | 1 => .disj | 2 => .leftOnly | _ => .rightOnly
def allPerms : List (List (Fin 7)) := [[0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 5, 6, 3, 4], [1, 0, 2, 4, 3, 6, 5], [1, 0, 2, 6, 5, 4, 3]]
def casesA : List (Fin 7) := [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 3, 3]
def casesB : List (Fin 7) := [1, 1, 1, 2, 2, 3, 3, 4, 4, 3, 4, 5, 6]
def casesOp : List Nat := [0, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1]
def tags : List Nat := [0, 0, 0, 0, 2, 6, 10, 12, 1, 14, 18, 1, 1, 22, 26, 1, 1, 30, 34, 1, 1, 23, 27, 1, 1, 31, 35, 1, 2, 6, 12, 10, 0, 0, 0, 0, 1, 16, 20, 1, 1, 32, 36, 1, 1, 24, 28, 1, 1, 33, 37, 1, 1, 25, 29, 1, 0, 14, 0, 18, 0, 16, 0, 20, 0, 0, 0, 0, 0, 38, 0, 1, 0, 40, 0, 1, 0, 39, 0, 1, 0, 41, 0, 1, 0, 22, 0, 26, 0, 32, 0, 36, 0, 38, 0, 1, 0, 0, 0, 0, 0, 42, 0, 1, 0, 46, 0, 1, 0, 50, 0, 1, 0, 30, 0, 34, 0, 24, 0, 28, 0, 40, 0, 1, 0, 42, 0, 1, 0, 0, 0, 0, 0, 51, 0, 1, 0, 48, 0, 1, 0, 23, 0, 27, 0, 33, 0, 37, 0, 39, 0, 1, 0, 46, 0, 1, 0, 51, 0, 1, 0, 0, 0, 0, 0, 43, 0, 1, 0, 31, 0, 35, 0, 25, 0, 29, 0, 41, 0, 1, 0, 50, 0, 1, 0, 48, 0, 1, 0, 43, 0, 1, 0, 0, 0, 0]
def numbered (i : Fin 13) : TraceGate SmallInput :=
  ⟨opAt (casesOp.getD i.val 0),raw7 (casesA.getD i.val 0),raw7 (casesB.getD i.val 0)⟩
def position (s : Fin 4) (j : Fin 7) := (allPerms.getD s.val []).getD j.val 0
def rowPerm (s : Fin 4) (r : SmallInput) := pack (fun j => raw7 (position s j) r)
def tag (x y : Fin 7) (op : Kind) := tags.getD (4*(7*x.val+y.val)+opIndex op) 0
def picked (n : Nat) : Fin 13 := ⟨((n-2)/4) % 13,Nat.mod_lt _ (by decide)⟩
def rotation (n : Nat) : Fin 4 := ⟨(n-2) % 4,Nat.mod_lt _ (by decide)⟩

theorem perm_graph : ∀ (s : Fin 4) (r : SmallInput), ans7 (rowPerm s r)=ans7 r := by decide +kernel

theorem raw_permute (s : Fin 4) (j : Fin 7) :
    restrict (rowPerm s) (raw7 j)=raw7 (position s j) :=
  funext (fun r => unpack (fun k => raw7 (position s k) r) j)

theorem dispatch_rules (op : Kind) : ∀ x y : Fin 7, x≠y →
    let n := tag x y op
    if n=0 then 2≤x.val ∧ ∀ b : Bool, applyKind op false b=false else
    if n=1 then 2≤y.val ∧ ∀ a : Bool, applyKind op a false=false else
    ∀r : SmallInput, applyKind op (raw7 x (rowPerm (rotation n) r)) (raw7 y (rowPerm (rotation n) r)) =
      (numbered (picked n)).value r := by
  cases op <;> decide +kernel

def Selected : Prop := (∃ n ws, n≤9 ∧ Free vertices7 n ws ∧ ans7∈ws) ∨
  ∃ i : Fin 13, ∃ n ws, n≤9 ∧ Free ((numbered i).value::vertices7) n ws ∧ ans7∈ws

theorem dispatch_head {g : TraceGate SmallInput} {gs : List (TraceGate SmallInput)}
    (ok : sufficient vertices7 ans7 (g::gs)) (fresh : freshTrace vertices7 (g::gs))
    (size : (g::gs).length≤10) : Selected := by
  classical
  obtain ⟨nL,nR,separate⟩ := fresh_ports g ok.1.1 ok.1.2.1 List.mem_cons_self fresh.1
  obtain ⟨x,ex⟩ := List.mem_ofFn.mp ((List.mem_cons.mp ok.1.1).resolve_left nL)
  obtain ⟨y,ey⟩ := List.mem_ofFn.mp ((List.mem_cons.mp ok.1.2.1).resolve_left nR)
  have xy : x≠y := fun e => separate (ex.symm.trans ((congrArg raw7 e).trans ey))
  have rx : reads g (raw7 x) := Or.inl ex.symm
  have ry : reads g (raw7 y) := Or.inr ey.symm
  let t := tag x y g.kind
  have rule := dispatch_rules g.kind x y xy
  change (if t=0 then _ else if t=1 then _ else _) at rule
  have n : gs.length≤9 := by simp only [List.length_cons] at size; omega
  by_cases a : t=0
  · rw [if_pos a] at rule
    have drop : restrict (minorLift x) g.value=absentBit := by
      funext r
      change applyKind g.kind (g.left (minorLift x r)) (g.right (minorLift x r))=false
      rw [←ex,←ey]
      have zero := congrFun (minor_off rule.1) r
      change raw7 x (minorLift x r)=false at zero
      rw [zero]
      exact rule.2 _
    obtain ⟨k,ws,h,run,out⟩ := absorbing_head ok fresh size xy rx ry rule.1 drop
    exact Or.inl ⟨k,ws,Nat.le_trans h n,run,out⟩
  · rw [if_neg a] at rule
    by_cases b : t=1
    · rw [if_pos b] at rule
      have drop : restrict (minorLift y) g.value=absentBit := by
        funext r
        change applyKind g.kind (g.left (minorLift y r)) (g.right (minorLift y r))=false
        rw [←ex,←ey]
        have zero := congrFun (minor_off rule.1) r
        change raw7 y (minorLift y r)=false at zero
        rw [zero]
        exact rule.2 _
      obtain ⟨k,ws,h,run,out⟩ := absorbing_head ok fresh size (Ne.symm xy) ry rx rule.1 drop
      exact Or.inl ⟨k,ws,Nat.le_trans h n,run,out⟩
    · rw [if_neg b] at rule
      let s := rotation t
      let i := picked t
      let pool := (numbered i).value::vertices7
      have eq : restrict (rowPerm s) g.value=(numbered i).value := by
        funext r
        change applyKind g.kind (g.left (rowPerm s r)) (g.right (rowPerm s r))=_
        rw [←ex,←ey]
        exact rule r
      have old : ∀ w∈g.value::vertices7, restrict (rowPerm s) w∈pool := by
        intro w hw
        rcases List.mem_cons.mp hw with z|h
        · subst w
          rw [eq]
          exact List.mem_cons_self
        rcases List.mem_cons.mp h with z|other
        · subst w
          exact List.mem_cons_of_mem _ List.mem_cons_self
        · obtain ⟨j,hj⟩ := List.mem_ofFn.mp other
          subst w
          rw [raw_permute]
          exact List.mem_cons_of_mem _ (raw_mem _)
      obtain ⟨ws,run,sub⟩ := restrict_trace (rowPerm s) gs ok.1.2.2 (Free.start (raw:=pool))
        (List.mem_cons_of_mem _ List.mem_cons_self) old
      have goal := sub ans7 ok.2
      have unchanged : restrict (rowPerm s) ans7=ans7 := funext (perm_graph s)
      rw [unchanged] at goal
      have account := accounted (rowPerm s) gs
      exact Or.inr ⟨i,_,ws,by omega,run,goal⟩

theorem select_program {n ws} (run : Free vertices7 n ws) (small : n≤10) (hit : ans7∈ws) :
    Selected := by
  obtain ⟨ts,len,well,eq⟩ := trace_of_free run
  obtain ⟨clean,solves,fresh,le,_⟩ := simplify_trace ts ⟨well,eq ▸ hit⟩
  cases clean with
  | nil =>
    have h : ans7∈vertices7 := solves.2
    rcases List.mem_cons.mp h with z|r
    · have test : ans7 (smallRow 5)=true := by decide
      exact Bool.noConfusion (test.symm.trans (congrFun z (smallRow 5)))
    · obtain ⟨i,e⟩ := List.mem_ofFn.mp r
      obtain ⟨s,d⟩ := seven_not_raw i
      exact (d (congrFun e.symm s)).elim
  | cons g gs => exact dispatch_head solves fresh (by omega)

end CoThetaSeven
namespace CoNatBench

def firstPairs : List (Nat×Nat) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6),(4,5),(4,6),(5,6)]
def secondPairs : List (Nat×Nat) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]

def rootWords : List Word := CoThetaBits.raw.map project
def nth (ws : List Word) (i : Nat) := ws.getD i (0,0)
def kinds (i : Nat) (x y : Word) : Word :=
  match i with | 0 => meet x y | 1 => join x y | 2 => skip x y | _ => skip y x

def firstWords (index : Nat) : List Word :=
  let pair := firstPairs[index/4]?.getD (0,1)
  let a := nth rootWords pair.1
  let b := nth rootWords pair.2
  let z := kinds (index % 4) a b
  z::a::b::(rootWords.filter (fun w => w != a && w != b))

def prefixCase (i j : Nat) : Bool :=
  let ws := firstWords i
  let p := secondPairs[j/16]?.getD (0,1)
  let a := nth ws p.1
  let b := nth ws p.2
  let z := kinds ((j/4) % 4) a b
  let rest := ws.filter (fun w => w != a && w != b)
  let next := match j % 4 with
    | 0 => z::rest
    | 1 => z::a::rest
    | 2 => z::b::rest
    | _ => z::a::b::rest
  if z == (0,0) || ws.contains z || next.length>9 || cover next != all then true
  else !(guardedSearch 8 next)

def casesBlock (i first count : Nat) : Bool :=
  (List.range count).all (fun d => prefixCase i (first+d))

end CoNatBench
namespace CoThetaSeven
open CoThetaFreeCore
open CoThetaNine (SmallInput raw7 ans7 vertices7 pack unpack toRows numeric_target)
open CoThetaBits (Row Wire den col Rep)

def numbers : List Nat := [0,1,2,5,6,9,10,13,14,45,61,65,69]
def numberedWord (i : Fin 13) :=
  CoThetaBits.gate (numbered i).kind (col (casesA.getD i.val 0)) (col (casesB.getD i.val 0))

def postPool (i : Fin 13) :=
  let a := col (casesA.getD i.val 0)
  let b := col (casesB.getD i.val 0)
  numberedWord i::a::b::CoThetaBits.trim a b CoThetaBits.raw

theorem post_data : ∀ i : Fin 13,
    (postPool i).Nodup ∧ ((postPool i).map CoNatBench.project)=CoNatBench.firstWords (numbers.getD i.val 0) ∧
    ((postPool i).Perm (numberedWord i::CoThetaBits.raw)) ∧
    ∀ j : Fin 7, CoThetaBits.coverage ((postPool i).filter fun v => v != col j)≠CoThetaBits.full := by
  decide +kernel

theorem proj_raw (j : Fin 7) : restrict toRows (raw7 j)=den (col j) :=
  funext (fun r => unpack (CoThetaBits.sample r) j)

theorem proj_head (i : Fin 13) : restrict toRows (numbered i).value=den (numberedWord i) := by
  rw [numberedWord,CoThetaBits.den_gate]
  funext r
  change applyKind (numbered i).kind (raw7 (casesA.getD i.val 0) (toRows r))
    (raw7 (casesB.getD i.val 0) (toRows r))=_
  change applyKind _ (raw7 _ (pack (CoThetaBits.sample r))) (raw7 _ (pack (CoThetaBits.sample r)))=_
  rw [unpack,unpack]
  rfl

theorem collect_init (i : Fin 13) {f : Row→Bool}
    (hf : f∈((numbered i).value::vertices7).map (restrict toRows)) :
    f=absentBit ∨ ∃ w∈postPool i, den w=f := by
  obtain ⟨v,hv,eq⟩ := List.mem_map.mp hf
  subst f
  have perm := (post_data i).2.2.1
  rcases List.mem_cons.mp hv with h|rest
  · subst v
    exact Or.inr ⟨_,perm.mem_iff.mpr List.mem_cons_self,(proj_head i).symm⟩
  rcases List.mem_cons.mp rest with h|final
  · subst v
    exact Or.inl rfl
  · obtain ⟨j,h⟩ := List.mem_ofFn.mp final
    subst v
    have mem : col j∈CoThetaBits.raw := by
      rw [←CoThetaBits.raw_is_ofFn]
      exact List.mem_ofFn.mpr ⟨j,rfl⟩
    exact Or.inr ⟨_,perm.mem_iff.mpr (List.mem_cons_of_mem _ mem),(proj_raw j).symm⟩

theorem classify_pool (i : Fin 13) {k S} (live : Live (den CoThetaBits.target) k S)
    (sub : ∀ f, S f → f=absentBit ∨ ∃w∈postPool i,den w=f) :
    Rep CoThetaBits.raw S ∨ Rep (postPool i) S := by
  classical
  have ng : den CoThetaBits.target≠absentBit := by
    intro bad
    have no := congrFun bad (true,0)
    simp [CoThetaBits.den_target,absentBit] at no
  have present (f) (h : S f) : ∃w∈postPool i,den w=f := by
    rcases sub f h with z|p
    · exact (live.excludes_zero ng (z ▸ h)).elim
    · exact p
  have core (j : Fin 7) : S (den (col j)) := by
    apply Classical.byContradiction
    intro missing
    apply (post_data i).2.2.2 j
    apply CoThetaBits.live_coverage _ live
    intro f hf
    obtain ⟨w,hw,eq⟩ := present f hf
    have ne : w≠col j := by
      intro same
      exact missing (same ▸ (eq ▸ hf))
    exact ⟨w,List.mem_filter.mpr ⟨hw,by simp [ne]⟩,eq⟩
  have raw_has {w : Wire} (hw : w∈CoThetaBits.raw) : S (den w) := by
    obtain ⟨j,e⟩ := CoThetaBits.indexed hw
    exact e ▸ core j
  have perm := (post_data i).2.2.1
  by_cases hit : S (den (numberedWord i))
  · right
    intro f
    refine ⟨present f,?_⟩
    rintro ⟨w,hw,eq⟩
    rcases List.mem_cons.mp (perm.mem_iff.mp hw) with z|r
    · subst w
      exact eq ▸ hit
    · exact eq ▸ raw_has r
  · left
    intro f
    constructor
    · intro hf
      obtain ⟨w,m,eq⟩ := present f hf
      rcases List.mem_cons.mp (perm.mem_iff.mp m) with e|r
      · subst w
        exact (hit (eq ▸ hf)).elim
      · exact ⟨w,r,eq⟩
    · rintro ⟨w,hw,eq⟩
      exact eq ▸ raw_has hw

def RawNine : Prop := ∀ {m S}, Live (den CoThetaBits.target) m S → m≤9 → Rep CoThetaBits.raw S → False
def AfterNine : Prop := ∀ i : Fin 13, ∀ {m S}, Live (den CoThetaBits.target) m S → m≤9 → Rep (postPool i) S → False

theorem impossible_after (r9 : RawNine) (p9 : AfterNine) (i : Fin 13)
    {n ws} (run : Free ((numbered i).value::vertices7) n ws) (n9 : n≤9) (out : ans7∈ws) : False := by
  let basis := ((numbered i).value::vertices7).map (restrict toRows)
  have zero : absentBit∈basis := List.mem_cons_of_mem _ List.mem_cons_self
  have goal := List.mem_map_of_mem (f:=restrict toRows) out
  rw [numeric_target] at goal
  obtain ⟨k,S,le,live,sub⟩ := rewind (run.map_rows toRows) zero
    (Live.stop (goal:=den CoThetaBits.target)) (fun w e => e.symm ▸ goal)
  rcases classify_pool i live (fun f hf => collect_init i (sub f hf)) with raw|extra
  · exact r9 live (by omega) raw
  · exact p9 i live (by omega) extra

theorem seven_bound (r9 : RawNine) (p9 : AfterNine) {n ws} (run : Free vertices7 n ws)
    (out : ans7∈ws) : 11≤n := by
  apply Classical.byContradiction
  intro ne
  rcases select_program run (by omega) out with ⟨h,ys,cost,reduced,goal⟩ | ⟨i,h,ys,cost,reduced,goal⟩
  · let raw0 := (vertices7.map (restrict toRows))
    have zero : absentBit∈raw0 := List.mem_cons_self
    have endw := List.mem_map_of_mem (f:=restrict toRows) goal
    rw [numeric_target] at endw
    obtain ⟨m,S,le,live,sub⟩ := rewind (reduced.map_rows toRows) zero
      (Live.stop (goal:=den CoThetaBits.target)) (fun w e => e.symm ▸ endw)
    have rep := CoThetaBits.root_rep live (by
      intro f hf
      obtain ⟨w,hw,eq⟩ := List.mem_map.mp (sub f hf)
      subst f
      rcases List.mem_cons.mp hw with z|l
      · subst w
        exact Or.inl rfl
      · obtain ⟨j,e⟩ := List.mem_ofFn.mp l
        subst w
        exact Or.inr ⟨j,(proj_raw j).symm⟩)
    exact r9 live (by omega) rep
  · exact impossible_after r9 p9 i reduced cost goal

end CoThetaSeven
namespace CoNatBench
open CoThetaFreeCore
open CoThetaBits (Wire Rep den gate)

def Supported (k : Nat) (ws : List Word) (a b : Word) (op : Kind) (ka kb : Bool) : Prop :=
  let z := wordGate op a b
  let out := extension ws a b op ka kb
  z≠(0,0) ∧ z∉ws ∧ out.length≤k+1 ∧ cover out=all ∧ guardedSearch k out=true

private theorem support_from {m k} {ws : List Wire} {x y : Wire} {U} (op : Kind)
    (nd : ws.Nodup) (ne : x≠y) (non : gate op x y≠CoThetaBits.zero) (fresh : gate op x y∉ws)
    (rep : Rep ws (ins (den x) (ins (den y) U)))
    (tail : Live (den CoThetaBits.target) m (ins (den (gate op x y)) U)) (enough : m≤k) :
    ∃ ka kb : Bool, Supported k (ws.map project) (project x) (project y) op ka kb := by
  classical
  let z := gate op x y
  let out := z::(CoThetaBits.kept x y U++CoThetaBits.trim x y ws)
  have ro : Rep out (ins (den z) U) := CoThetaBits.edit_rep rep
  have d : out.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,CoThetaBits.edit_distinct ne nd⟩
    intro hz
    exact fresh ((seen_iff rep z).2 (Or.inr (Or.inr ((CoThetaBits.edit_member rep).1 hz))))
  let ka := decide (U (den x))
  let kb := decide (U (den y))
  have em : out.map project=extension (ws.map project) (project x) (project y) op ka kb :=
    project_edit ws x y op U
  refine ⟨ka,kb,?_,?_,?_,?_,?_⟩
  · rw [←project_gate]
    intro e
    apply non
    apply project_inj
    simpa [project,CoThetaBits.zero] using e
  · rw [←project_gate]
    intro h
    obtain ⟨v,hv,e⟩ := List.mem_map.mp h
    exact fresh (project_inj e ▸ hv)
  · rw [←em,List.length_map]
    have b := CoThetaBits.state_width tail d ro
    omega
  · rw [←em,project_cover,CoThetaBits.live_coverage out tail (fun w h => (ro w).1 h)]
    rfl
  · rw [←em]
    exact guarded_complete tail k enough out d ro

theorem supported_step {m k S} {ws : List Wire} (run : Live (den CoThetaBits.target) m S)
    (nd : ws.Nodup) (rep : Rep ws S) (size : m≤k+1) (stop : CoThetaBits.target∉ws) :
    ∃ i j : Nat, i<j ∧ j<ws.length ∧ ∃ op : Kind, ∃ ka kb : Bool,
      Supported k (ws.map project) (nth (ws.map project) i) (nth (ws.map project) j) op ka kb := by
  classical
  cases run with
  | stop => exact (stop ((seen_iff rep CoThetaBits.target).2 rfl)).elim
  | @step m U a b op ab ha hb fresh tail =>
    obtain ⟨x,hx,ex⟩ := (rep a).1 (Or.inl rfl)
    obtain ⟨y,hy,ey⟩ := (rep b).1 (Or.inr (Or.inl rfl))
    subst a
    subst b
    let z := gate op x y
    have e : den z=(fun i => applyKind op (den x i) (den y i)) := CoThetaBits.den_gate _ _ _
    have ne : x≠y := fun eq => ab (congrArg den eq)
    have rest : Live (den CoThetaBits.target) m (ins (den z) U) := by rw [e]; exact tail
    have ng : den CoThetaBits.target≠absentBit := by
      intro h
      have bad := congrFun h (true,0)
      simp [CoThetaBits.den_target,absentBit] at bad
    have non : z≠CoThetaBits.zero := by
      intro h
      exact rest.excludes_zero ng (Or.inl (((congrArg den h).trans CoThetaBits.den_zero).symm))
    have nf : z∉ws := fun h => fresh (e ▸ (seen_iff rep z).1 h)
    obtain ⟨i,hi,vi⟩ := List.mem_iff_getElem.mp hx
    obtain ⟨j,hj,vj⟩ := List.mem_iff_getElem.mp hy
    have i_ne : i≠j := by intro h; subst j; exact ne (vi.symm.trans vj)
    have each (l : Nat) (h : l<ws.length) :
        nth (ws.map project) l=project ws[l] := by
      simp [nth,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem h]
    by_cases order : i<j
    · refine ⟨i,j,order,hj,op,?_⟩
      rw [each i hi,each j hj,vi,vj]
      exact support_from op nd ne non nf rep rest (by omega)
    · refine ⟨j,i,by omega,hi,reflectOp op,?_⟩
      rw [each j hj,each i hi,vj,vi]
      have sw : gate (reflectOp op) y x=z := by apply project_inj; simp [z,project_gate,gate_swap]
      apply support_from (reflectOp op) nd (Ne.symm ne) <;> try rw [sw]
      · exact non
      · exact nf
      · intro w
        simpa [ins,or_left_comm] using rep w
      · exact rest
      · omega

end CoNatBench
namespace CoThetaSeven
open CoThetaFreeCore CoNatBench
open CoThetaBits (Wire Row Rep den)

def keepIndex (a b : Bool) : Nat := a.toNat+2*b.toNat

theorem pair7_index : ∀ a b : Fin 7, a.val<b.val →
    ∃ q : Fin 21, firstPairs[q.val]?.getD (0,1)=(a.val,b.val) := by decide +kernel

theorem pair8_index : ∀ a b : Fin 8, a.val<b.val →
    ∃ q : Fin 28, secondPairs[q.val]?.getD (0,1)=(a.val,b.val) := by decide +kernel

theorem first_keep (op : Kind) : ∀ a b : Fin 7, a.val<b.val → ∀ ka kb : Bool,
    cover (extension rootWords (nth rootWords a.val) (nth rootWords b.val) op ka kb)=all → ka=true ∧ kb=true := by
  cases op <;> decide +kernel

theorem first_repr (op : Kind) (q : Fin 21) :
    let pair := firstPairs[q.val]?.getD (0,1)
    extension rootWords (nth rootWords pair.1) (nth rootWords pair.2) op true true =
    firstWords (4*q.val+opIndex op) := by
  revert q
  cases op <;> decide +kernel

theorem class_data : ∀ i : Fin 13, (postPool i).length=8 ∧ CoThetaBits.target∉postPool i := by decide +kernel
theorem target_out : CoThetaBits.target∉CoThetaBits.raw := by decide +kernel

theorem root_from_cases (checks : ∀ i : Fin 84, guardedSearch 8 (firstWords i.val)=false) : RawNine := by
  intro m S live cost rep
  obtain ⟨a,b,ab,limit,op,ka,kb,hit⟩ := supported_step live CoThetaBits.raw_nodup rep cost target_out
  change b<7 at limit
  let u : Fin 7 := ⟨a,by omega⟩
  let v : Fin 7 := ⟨b,limit⟩
  obtain ⟨q,eq⟩ := pair7_index u v ab
  obtain ⟨_,_,_,cov,more⟩ := hit
  obtain ⟨k1,k2⟩ := first_keep op u v ab ka kb cov
  subst ka
  subst kb
  have link := first_repr op q
  change firstPairs[q.val]?.getD (0,1)=(a,b) at eq
  rw [eq] at link
  change guardedSearch 8 (extension rootWords (nth rootWords a) (nth rootWords b) op true true)=true at more
  rw [link] at more
  have bound : 4*q.val+opIndex op<84 := by
    have h := q.isLt
    cases op <;> simp [opIndex] <;> omega
  exact Bool.false_ne_true ((checks ⟨_,bound⟩).symm.trans more)

theorem digits (q : Nat) (op : Kind) (ka kb : Bool) :
    let n := 16*q+4*opIndex op+keepIndex ka kb
    n/16=q ∧ (n/4) % 4=opIndex op ∧ n % 4=keepIndex ka kb := by
  cases op <;> cases ka <;> cases kb <;> simp [opIndex,keepIndex] <;> omega

theorem bits_op (op : Kind) (a b : Word) : kinds (opIndex op) a b=wordGate op a b := by cases op <;> rfl

theorem prefix_conflict (label q : Nat) (qBound : q<28) {a b : Nat}
    (pair : secondPairs[q]?.getD (0,1)=(a,b)) (op : Kind) (ka kb : Bool)
    (hit : Supported 8 (firstWords label) (nth (firstWords label) a) (nth (firstWords label) b) op ka kb) :
    ∃ j : Fin 448, prefixCase label j.val=false := by
  let j := 16*q+4*opIndex op+keepIndex ka kb
  have cap : j<448 := by cases op <;> cases ka <;> cases kb <;> simp [j,opIndex,keepIndex] <;> omega
  refine ⟨⟨j,cap⟩,?_⟩
  obtain ⟨hq,ho,hk⟩ := digits q op ka kb
  change j/16=q at hq
  change (j/4) % 4=opIndex op at ho
  change j % 4=keepIndex ka kb at hk
  obtain ⟨non,fresh,width,cov,yes⟩ := hit
  simp only [prefixCase,hq,ho,hk,pair,bits_op,Prod.fst,Prod.snd]
  cases ka <;> cases kb <;>
    simp [extension,keepList,restOf] at width cov yes <;>
    simp [keepIndex,restOf,non,fresh,Nat.not_lt_of_ge width,cov,yes]

theorem after_from_cases (checks : ∀ i : Fin 13, ∀ j : Fin 448, prefixCase (numbers.getD i.val 0) j.val=true) :
    AfterNine := by
  intro i m S live bound rep
  obtain ⟨n,stop⟩ := class_data i
  obtain ⟨a,b,ab,lb,op,ka,kb,hit⟩ := supported_step live (post_data i).1 rep bound stop
  rw [n] at lb
  obtain ⟨q,eq⟩ := pair8_index ⟨a,by omega⟩ ⟨b,lb⟩ ab
  rw [(post_data i).2.1] at hit
  obtain ⟨j,fault⟩ := prefix_conflict (numbers.getD i.val 0) q.val q.isLt eq op ka kb hit
  exact Bool.false_ne_true (fault.symm.trans (checks i j))

theorem combine_blocks (tests : ∀ i : Fin 13, ∀ b : Fin 38,
    casesBlock (numbers.getD i.val 0) (12*b.val) (min 12 (448-12*b.val))=true) :
    ∀ i : Fin 13, ∀ j : Fin 448, prefixCase (numbers.getD i.val 0) j.val=true := by
  intro i j
  let b : Fin 38 := ⟨j.val/12,by have h := j.isLt; omega⟩
  have all := tests i b
  have d : j.val % 12 < min 12 (448-12*b.val) := by
    have h := j.isLt
    dsimp [b]
    omega
  have yes := List.all_eq_true.mp all (j.val % 12) (List.mem_range.mpr d)
  have eq : 12*b.val+j.val % 12=j.val := by dsimp [b]; omega
  exact eq ▸ yes

end CoThetaSeven

namespace CoThetaNine
open CoThetaFreeCore

noncomputable local instance {ρ : Type} : DecidableEq (TraceGate ρ) := Classical.decEq _

def slice04 (r : Fin 128) : Input := row (CoPetersenThetaGeometry.plant 0 r.val)
def or04 : TraceGate Input := ⟨.disj,vtx 0,vtx 4⟩
def and03 : TraceGate Input := ⟨.conj,vtx 0,vtx 3⟩

def fixedHeadResult (gate : TraceGate Input) (gs : List (TraceGate Input)) : Prop :=
  (∃ n ys, n ≤ gs.length ∧ Free vertices n ys ∧ ans∈ys) ∨
  ∃ ts, ts.length≤gs.length ∧ sufficient vertices ans (gate::ts) ∧ 4 ≤ saved slice04 (gate::ts)

private theorem threeSet {gs : List (TraceGate Input)} {p q : Input→Bool}
    (h : ThreeReaders (fun g => reads g p ∨ reads g q) gs) :
    3 ≤ (readerSet gs p ∪ readerSet gs q).card := by
  classical
  obtain ⟨a,ha,b,hb,c,hc,ra,rb,rc,ab,ac,bc⟩ := h
  let S := readerSet gs p ∪ readerSet gs q
  have ins (g : TraceGate Input) (hg : g∈gs) (hr : reads g p ∨ reads g q) : g∈S := by
    rcases hr with r|r
    · exact Finset.mem_union_left _ (mem_readerSet.mpr ⟨hg,r⟩)
    · exact Finset.mem_union_right _ (mem_readerSet.mpr ⟨hg,r⟩)
  have sub : ({a,b,c} : Finset (TraceGate Input)) ⊆ S := by
    intro g hg
    simp only [Finset.mem_insert,Finset.mem_singleton] at hg
    rcases hg with rfl|rfl|rfl
    · exact ins _ ha ra
    · exact ins _ hb rb
    · exact ins _ hc rc
  have bound := Finset.card_le_card sub
  simpa [Finset.card_insert_of_notMem,ab,ac,bc,S] using bound

private theorem fixedHead04 {gate : TraceGate Input} (gs : List (TraceGate Input))
    {j : Fin 9} (different : (0 : Fin 9) ≠ j) (hp : reads gate (vtx 0))
    (hj : reads gate (vtx j)) (headZero : restrict slice04 gate.value = absentBit)
    (headDistinct : gate.value ≠ vtx 0 ∧ gate.value ≠ vtx 4)
    (correct : sufficient vertices ans (gate::gs)) : fixedHeadResult gate gs := by
  classical
  have init : sufficient (gate.value::vertices) ans gs := ⟨correct.1.2.2,correct.2⟩
  obtain ⟨ts,⟨reg,out⟩,fresh,le,_⟩ := simplify_trace gs init
  have well : registered vertices (gate::ts) := ⟨correct.1.1,correct.1.2.1,reg⟩
  have result : ans∈traceWires vertices (gate::ts) := out
  by_cases live : UsePath ts gate.value ans
  · have rz (i : Fin 9) : vtx i∈vertices :=
      List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
    have pz : restrict slice04 (vtx 0)=absentBit := by
      funext y
      exact (by decide +kernel : ∀ y : Fin 128, vtx 0 (slice04 y)=false) y
    have qz : restrict slice04 (vtx 4)=absentBit := by
      funext y
      exact (by decide +kernel : ∀ y : Fin 128, vtx 4 (slice04 y)=false) y
    have nz : restrict slice04 ans ≠ absentBit := by
      intro e
      exact (by decide : ans (slice04 5) ≠ false) (congrFun e (5 : Fin 128))
    have aliases (g : TraceGate Input) (hg : g∈ts) : g.value≠vtx 0 ∧ g.value≠vtx 4 := by
      have h := fresh_outputs fresh g hg
      exact ⟨fun e => h (List.mem_cons_of_mem _ (e ▸ rz 0)),
             fun e => h (List.mem_cons_of_mem _ (e ▸ rz 4))⟩
    obtain ⟨x,hx,rx,neq⟩ := another_raw_reader different (gate::ts) gate hp hj well result
    have three := three_for_pair 0 well result
      (Or.inl ⟨gate,List.mem_cons_self,x,hx,hp,rx,neq.symm⟩)
    obtain ⟨g,mem,hp',hq',van⟩ := extra_loss_on_path slice04 pz qz aliases live headZero headDistinct nz
    exact Or.inr ⟨ts,le,⟨well,result⟩,four_saved_raw_head slice04 _ _ _ pz qz (threeSet three)
       ⟨g,List.mem_cons_of_mem _ mem,hp',hq',van⟩⟩
  · obtain ⟨n,ws,hn,run,mem⟩ := omit_dead_head vertices ts gate.value ans reg out live
    exact Or.inl ⟨n,ws,hn.trans le,run,mem⟩

theorem fixed_or04 (gs : List (TraceGate Input)) (h : sufficient vertices ans (or04::gs)) :
    fixedHeadResult or04 gs := by
  apply fixedHead04 gs (j:=4) (by decide) (Or.inl rfl) (Or.inr rfl) _ _ h
  · funext y
    exact (by decide +kernel : ∀ y : Fin 128, or04.value (slice04 y)=false) y
  · exact ⟨fun e => (by decide : or04.value (row 16) ≠ vtx 0 (row 16)) (congrFun e (row 16)),
           fun e => (by decide : or04.value (row 1) ≠ vtx 4 (row 1)) (congrFun e (row 1))⟩

theorem fixed_and03 (gs : List (TraceGate Input)) (h : sufficient vertices ans (and03::gs)) :
    fixedHeadResult and03 gs := by
  apply fixedHead04 gs (j:=3) (by decide) (Or.inl rfl) (Or.inr rfl) _ _ h
  · funext y
    exact (by decide +kernel : ∀ y : Fin 128, and03.value (slice04 y)=false) y
  · exact ⟨fun e => (by decide : and03.value (row 1) ≠ vtx 0 (row 1)) (congrFun e (row 1)),
           fun e => (by decide : and03.value (row 16) ≠ vtx 4 (row 16)) (congrFun e (row 16))⟩

end CoThetaNine

namespace CoThetaNine
open CoThetaFreeCore
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem fixed_head_lower (cert : SignedLower)
    {head : TraceGate Input} {gs : List (TraceGate Input)} (h : fixedHeadResult head gs) :
    14≤gs.length := by
  rcases h with ⟨n,zs,le,run,out⟩|⟨ts,le,solves,saves⟩
  · obtain ⟨s,len,reg,eq⟩ := trace_of_free run
    have h := any_nine_lower cert (gs:=s) ⟨reg,eq ▸ out⟩
    omega
  · have lower := residual_at_least_eleven cert 0 solves
    have total := accounted (sliceLift 0) (head::ts)
    change 4≤saved (sliceLift 0) (head::ts) at saves
    simp only [List.length_cons] at total
    omega

end CoThetaNine


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

namespace CoThetaFreeCore

theorem run_append {ρ : Type} (a b : List PinForm) (start : List (ρ→Bool)) :
    execute (a++b) start = execute b (execute a start) := by
  induction a generalizing start with
  | nil => rfl
  | cons f fs ih => exact ih _

theorem cost_append (a b : List PinForm) : cost (a++b)=cost a+cost b := by
  induction a with
  | nil => simp [cost]
  | cons x xs ih => simp [cost,ih,Nat.add_assoc]

theorem pin_cost_length (fs : List PinForm) : cost fs≤fs.length := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    cases f <;> simp only [cost,PinForm.binaryCost,List.length_cons] <;> omega

end CoThetaFreeCore

namespace CoThetaNine
open CoThetaFreeCore CoThetaPhysical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem fan_of_mono (C : Circuit) (h : Monotone2 C) : FanInTwo C := by
  intro g hg
  obtain ⟨op,arity⟩ := h g hg
  refine ⟨?_,arity⟩
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢
  exact op.elim Or.inl (fun e => Or.inr (Or.inl e))

end CoThetaNine

namespace CoThetaNine
open CoThetaFreeCore CoThetaPhysical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def tailInputs03 : List (Input→Bool) := List.ofFn vtx ++ [and03.value]
def seed03 : List (Input→Bool) := absentBit::(fun _ => true)::tailInputs03

theorem norm_inputs03 : ∀ f∈seed03.map (norm (row 0)), f∈and03.value::vertices := by
  intro f hf
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hf
  have hz : absentBit∈and03.value::vertices := List.mem_cons_of_mem _ List.mem_cons_self
  rcases List.mem_cons.mp ht with t0|ht
  · subst t
    exact hz
  rcases List.mem_cons.mp ht with t1|ht
  · subst t
    exact hz
  rcases List.mem_append.mp ht with hin|head
  · obtain ⟨i,e⟩ := List.mem_ofFn.mp hin
    subst t
    have lo : ∀ j : Fin 9, vtx j (row 0)=false := by decide
    have eq : norm (row 0) (vtx i)=vtx i := by
      funext r
      simp [CoThetaFreeCore.norm,lo,phase]
    rw [eq]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
  · obtain rfl := List.mem_singleton.mp head
    have lo : and03.value (row 0)=false := by decide
    have eq : norm (row 0) and03.value=and03.value := by
      funext r
      simp [CoThetaFreeCore.norm,lo,phase]
    exact eq ▸ List.mem_cons_self

theorem nonedge_trace (D : Circuit) (fan : FanInTwo D)
    (correct : ∀ r : Input, D.eval (List.ofFn (fun i => vtx i r) ++ [vtx 0 r && vtx 3 r])=ans r) :
    ∃ gs, gs.length ≤ cost (D.gates.map gateForm) ∧ sufficient vertices ans (and03::gs) := by
  let fs := D.gates.map gateForm
  let result := (execute fs tailInputs03).getD D.output absentBit
  have ep (r : Input) : tailInputs03.map (fun f => f r)=
      List.ofFn (fun i => vtx i r) ++ [vtx 0 r && vtx 3 r] := by
    simp [tailInputs03,List.map_ofFn,and03,TraceGate.value,applyKind]
  have correctWord : result=ans := by
    funext r
    have h := circuit_rows D fan tailInputs03 r
    have read := congrArg (fun ws : List Bool => ws.getD D.output false) h
    change ((execute fs tailInputs03).map (fun f => f r)).getD D.output false=_ at read
    have eq (w : List (Input→Bool)) (i : Nat) :
        (w.map (fun f => f r)).getD i false = w.getD i absentBit r := by
      simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
      cases w[i]? <;> rfl
    rw [eq,ep] at read
    exact read.trans (correct r)
  have present : result∈execute fs tailInputs03 := by
    cases e : (execute fs tailInputs03)[D.output]? with
    | none =>
      have no : result=absentBit := by simp [result,List.getD_eq_getElem?_getD,e]
      exact (ans_not_zero (correctWord.symm.trans no)).elim
    | some w =>
      have eq : result=w := by simp [result,List.getD_eq_getElem?_getD,e]
      exact (congrArg (fun v => v∈execute fs tailInputs03) eq).mpr (List.mem_of_getElem? e)
  have cs (b : Bool) : (fun _ : Input => b)∈seed03 := by
    cases b
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
  obtain ⟨ys,program,cover⟩ := pins_to_program fs tailInputs03 seed03 seed03 0 Ordinary.start cs
    (fun w h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
  obtain ⟨zs,free,sub⟩ := simulate_all_wires (row 0) program
  have hnorm : norm (row 0) ans=ans := by
    have lo : ans (row 0)=false := by decide
    funext r
    simp [CoThetaFreeCore.norm,lo,phase]
  have goalIn := sub result (cover _ present)
  rw [correctWord,hnorm] at goalIn
  obtain ⟨gs,len,reg,eq⟩ := trace_of_free free
  have switch := trace_subset gs norm_inputs03
  have here : ans∈traceWires (and03.value::vertices) gs := switch.2 ans (eq ▸ goalIn)
  refine ⟨gs,?_,⟨⟨?_,?_,switch.1 reg⟩,here⟩⟩
  · simpa [fs] using le_of_eq len
  · exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨0,rfl⟩)
  · exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨3,rfl⟩)

theorem cost_with_not (gs : List Gate) (hasNOT : ∃ g∈gs, g.op = GateOp.not) :
    cost (gs.map gateForm) + 1 ≤ gs.length := by
  induction gs with
  | nil => simp at hasNOT
  | cons g gs ih =>
    obtain ⟨u,hu,op⟩ := hasNOT
    have rest := pin_cost_length (gs.map gateForm)
    simp only [List.length_map] at rest
    have small := form_cost_le g
    rcases List.mem_cons.mp hu with rfl|inside
    · rw [boolCost,op] at small
      change (gateForm u).binaryCost ≤ 0 at small
      simp only [List.map_cons,cost,List.length_cons]
      omega
    · have h := ih ⟨u,inside,op⟩
      have one : boolCost g≤1 := by cases e : g.op <;> simp [boolCost,e]
      simp only [List.map_cons,cost,List.length_cons]
      omega

end CoThetaNine

open PEqualNP.CircuitLowerBounds

namespace WireMono


def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → value C x r = true → value C y r = true) :
    value C x (n + k) = true → value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  have hy := gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then value C x r else false) = true →
      (if r < n + k then value C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

abbrev AO (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma wires_mono {n : ℕ} (C : Circuit) (hAO : AO C) (x y : Fin n → Bool)
    (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · let p : Fin n := ⟨w, hw⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases h : w < n + C.size
    · let k := w - n
      have hk : k < C.gates.length := by dsimp [k]; unfold Circuit.size at h; omega
      have hwk : w = n + k := by dsimp [k]; omega
      rw [hwk]
      refine gate_mono C k hk (hAO _ (List.getElem_mem hk)).1 x y ?_
      intro r _ hr
      exact ih r (by omega)
    · rw [missing_value C x w (by omega)]
      simp

end WireMono

namespace PhysicalHead

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem preserved (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem atEnd (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

theorem firstValue {n : ℕ} (g : Gate) (tail : List Gate) (o : ℕ) (x : Fin n → Bool) :
    (Circuit.wires ⟨g :: tail,o⟩ (List.ofFn x)).getD n false =
      g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) := by
  let w := List.ofFn x
  have hl : w.length = n := by simp [w]
  change (tail.foldl step (step w g)).getD n false = _
  rw [preserved tail (step w g) n (by simp [step, hl])]
  simpa only [step, w, List.length_ofFn] using atEnd (List.ofFn x) (g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false))

theorem emptyHead {n : ℕ} (o : ℕ) (x : Fin n → Bool) :
    (Circuit.wires ⟨[],o⟩ (List.ofFn x)).getD n false = false := by
  change (List.ofFn x).getD n false = false
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp : (List.ofFn x).length ≤ n)] <;> rfl

theorem semanticTail {n : ℕ} (g : Gate) (tail : List Gate) (o : ℕ) (x : Fin n → Bool)
    (b : Bool) (head : (Circuit.wires ⟨g :: tail,o⟩ (List.ofFn x)).getD n false = b) :
    Circuit.eval ⟨g :: tail,o⟩ (List.ofFn x) =
      Circuit.eval ⟨tail,o⟩ (List.ofFn x ++ [b]) := by
  have h := (firstValue g tail o x).symm.trans head
  change (tail.foldl step (List.ofFn x ++ [g.op.eval (g.inputs.map fun i =>
    (List.ofFn x).getD i false)])).getD o false = _
  rw [h]
  rfl

theorem of_tail_bound {n k : ℕ} (h f : (Fin n → Bool) → Bool)
    (hnonzero : ∃ x, h x = true)
    (tailBound : ∀ D : Circuit, FanInTwo D →
      (∀ x, D.eval (List.ofFn x ++ [h x]) = f x) → k ≤ D.size) :
    ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD n false = h x) →
      circuitFun n C = f → k + 1 ≤ C.size := by
  intro C hfan hhead hfun
  obtain ⟨gs,o⟩ := C
  cases gs with
  | nil =>
    obtain ⟨x, hx⟩ := hnonzero
    have bad := hhead x
    rw [emptyHead, hx] at bad <;> cases bad
  | cons g tail =>
    let D : Circuit := ⟨tail,o⟩
    have hf : FanInTwo D := by
      intro gate hmem
      exact hfan gate (List.mem_cons_of_mem g hmem)
    have he : ∀ x, D.eval (List.ofFn x ++ [h x]) = f x := by
      intro x
      exact (semanticTail g tail o x (h x) (hhead x)).symm.trans (congrFun hfun x)
    have hs := tailBound D hf he
    change k ≤ tail.length at hs
    change k + 1 ≤ tail.length + 1
    exact Nat.add_le_add_right hs 1

theorem of_fourteen_gate_tests (h f : (Fin 9 → Bool) → Bool) (hnonzero : ∃ x, h x = true)
    (tests : ∀ D : Circuit, FanInTwo D → D.size ≤ 14 →
      ∃ x, D.eval (List.ofFn x ++ [h x]) ≠ f x) :
    ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = h x) →
      circuitFun 9 C = f → 16 ≤ C.size := by
  apply of_tail_bound (k := 15) h f hnonzero
  intro D hfan hall
  by_contra hn
  obtain ⟨x,hx⟩ := tests D hfan (by omega)
  exact hx (hall x)

theorem not_zero_witness : ∃ x : Fin 9 → Bool, !(x 0) = true := ⟨fun _ => false, rfl⟩

theorem and_zero_one_witness : ∃ x : Fin 9 → Bool, (x 0 && x 1) = true := ⟨fun _ => true, rfl⟩

end PhysicalHead

namespace CoActual1669
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PhysicalHead
open WireMono
abbrev Source := Fin 9 → Bool
def edge (x : Source) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
def head03 (x : Source) : Bool := x 0 && x 3
def tailF (D : Circuit) (x : Source) (b : Bool) := D.eval (List.ofFn x ++ [b])
def edgeGate : Gate := ⟨GateOp.and,[0,1]⟩

abbrev EdgeLower := ∀ C : Circuit, FanInTwo C →
  (∀ x : Source, (C.wires (List.ofFn x)).getD 9 false = (x 0 && x 1)) →
  circuitFun 9 C=edge → 16≤C.size

private theorem realHead (D : Circuit) (x : Source) :
    (Circuit.wires ⟨edgeGate::D.gates,D.output⟩ (List.ofFn x)).getD 9 false = (x 0 && x 1) := by
  rw [firstValue]
  simp [edgeGate,GateOp.eval,List.getD_eq_getElem?_getD,List.getElem?_ofFn]

private theorem snocList (x : Source) (b : Bool) :
    List.ofFn (Fin.snoc x b : Fin 10 → Bool) = List.ofFn x ++ [b] := by
  rw [List.ofFn_succ']
  simp [Fin.snoc]

private theorem tail_mono (D : Circuit) (ao : AO D) (x y : Source) (a b : Bool)
    (le : ∀ i, x i = true → y i = true) (ab : a = true → b = true) :
    tailF D x a = true → tailF D y b = true := by
  have h : ∀ i, (Fin.snoc x a : Fin 10 → Bool) i = true → (Fin.snoc y b : Fin 10 → Bool) i = true := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using ab
    · simpa only [Fin.snoc_castSucc] using le j
  have g := wires_mono D ao (Fin.snoc x a) (Fin.snoc y b) h D.output
  change D.eval (List.ofFn (Fin.snoc x a : Fin 10 → Bool)) = true →
    D.eval (List.ofFn (Fin.snoc y b : Fin 10 → Bool)) = true at g
  simpa only [tailF,snocList] using g

def edges : List (Fin 9 × Fin 9) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
def pair (e : Fin 9 × Fin 9) (i : Fin 9) : Bool := decide (i=e.1 ∨ i=e.2)

private theorem edge_witness {x : Source} (hx : edge x=true) :
    ∃ y : Source, (∀ i, y i=true → x i=true) ∧ edge y=true ∧ head03 y=false := by
  have ex : edges.any (fun e => x e.1 && x e.2)=true := by
    simpa [edge,edges,Bool.or_assoc] using hx
  obtain ⟨p,hp,ht⟩ := List.any_eq_true.mp ex
  have concrete : ∀ e∈edges, edge (pair e)=true ∧ head03 (pair e)=false := by decide +kernel
  refine ⟨pair p,?_,concrete _ hp⟩
  intro i h
  have hb := Bool.and_eq_true_iff.mp ht
  rcases of_decide_eq_true h with eq|eq
  · simpa [eq] using hb.1
  · simpa [eq] using hb.2

private theorem monotone_bound (deadCase : Prior1667.Impossible Prior1667.graph 14 Prior1667.inputs.toFinset) (D : Circuit) (fan : FanInTwo D) (ao : AO D)
    (correct : ∀ x, tailF D x (head03 x)=edge x) : 15 ≤ D.size := by
  have zeroSlot (x : Source) : tailF D x false=edge x := by
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro h
      rw [←correct]
      exact tail_mono D ao x x false (head03 x) (fun _ => id) (by simp) h
    · intro h
      obtain ⟨y,le,yes,no⟩ := edge_witness h
      have atY := (correct y).trans yes
      rw [no] at atY
      exact tail_mono D ao y x false false le id atY
  exact Prior1667.zero_suffix
    deadCase D fan zeroSlot

theorem original_given (deadCase : Prior1667.Impossible Prior1667.graph 14 Prior1667.inputs.toFinset) (lower7 : CoThetaNine.SignedLower) :
    ∀ C : Circuit, FanInTwo C →
    (∀ x : Source, (C.wires (List.ofFn x)).getD 9 false=head03 x) →
    circuitFun 9 C=edge → 16≤C.size := by
  apply of_tail_bound (k:=15) head03 edge ⟨fun _ => true,rfl⟩
  intro D fan correct
  by_cases neg : ∃ g∈D.gates, g.op=GateOp.not
  · obtain ⟨gs,le,solves⟩ := CoThetaNine.nonedge_trace D fan (fun r =>
      correct (fun i => CoThetaNine.vtx i r))
    have bound := CoThetaNine.fixed_head_lower lower7 (CoThetaNine.fixed_and03 gs solves)
    have save := CoThetaNine.cost_with_not D.gates neg
    change 15 ≤ D.gates.length
    omega
  · have ao : AO D := by
      intro g hg
      obtain ⟨op,count⟩ := fan g hg
      refine ⟨?_,count⟩
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op
      rcases op with a|b|c
      · exact Or.inl a
      · exact Or.inr b
      · exact (neg ⟨g,hg,c⟩).elim
    exact monotone_bound deadCase D fan ao correct
end CoActual1669
end PEqualNP.Outside.L_meta_1669

open PEqualNP.Outside.L_meta_1669 in
theorem Co1669LayoutConclusion (deadCase : Prior1667.Impossible Prior1667.graph 14 Prior1667.inputs.toFinset) (lower : CoThetaNine.SignedLower) : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 3)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  exact CoActual1669.original_given deadCase lower
