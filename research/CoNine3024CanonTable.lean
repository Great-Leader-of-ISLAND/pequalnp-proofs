import PEqualNP.CoNine3024Canon
import PEqualNP.CoNine3024PairProgram

namespace CoNine3024.Canon

abbrev Oracle := Nat → State → Option CoNine3024PairGuard.Hint

def guided (p : Fin 11) (ask : Oracle) (k : Nat) (s : State) : Bool :=
  !(s.wires.length==k+1 && (ask k s).any (CoNine3024PairGuard.verify p s.wires))

structure Table where
  size : Nat
  state : Nat → State
  slot : State → Nat

def valid (guard : Nat → State → Bool) (g : Geometry) (k : Nat) (t : Table) : Prop :=
  ∀ i<t.size,run guard g k (t.state i)=false

def hit (t : Table) (s : State) := decide (t.slot s<t.size) && decide (t.state (t.slot s)=s)

theorem hit_false {guard g k t s} (proved : valid guard g k t) (h : hit t s=true) :
    run guard g k s=false := by
  simp only [hit,Bool.and_eq_true,decide_eq_true_eq] at h
  simpa only [h.2] using proved _ h.1

def closed (guard : Nat → State → Bool) (g : Geometry) (k : Nat) (s : State) : Bool :=
  !(live g s) && (decide (k=0) || !(guard k s && safe s))

theorem closed_false {guard g k s} (h : closed guard g k s=true) : run guard g k s=false := by
  cases k with
  | zero =>
    change live g s=false
    simpa [closed] using h
  | succ k =>
    unfold closed at h
    simp only [Nat.succ_ne_zero,decide_false,Bool.false_or,Bool.and_eq_true,Bool.not_eq_true'] at h
    simp only [run,h.1,h.2,Bool.false_and,Bool.false_or]

def node (guard : Nat → State → Bool) (g : Geometry) (k : Nat) (succ : Table) (s : State) : Bool :=
  !(live g s) && (!(guard (k+1) s && safe s) || (children g k s).all fun raw =>
    let t := order raw
    hit succ t || closed guard g k t)

theorem node_false {guard g k t s} (proved : valid guard g k t) (h : node guard g k t s=true) :
    run guard g (k+1) s=false := by
  simp only [node,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true'] at h
  apply Bool.eq_false_iff.mpr
  intro yes
  simp only [run,Bool.or_eq_true,Bool.and_eq_true] at yes
  rcases yes with done|⟨ok,move⟩
  · exact Bool.false_ne_true (h.1.symm.trans done)
  rcases h.2 with no|checked
  · exact Bool.false_ne_true (no.symm.trans (by simpa only [Bool.and_eq_true] using ok))
  obtain ⟨raw,edge,tail⟩ := List.any_eq_true.mp move
  have checkedChild := List.all_eq_true.mp checked raw edge
  simp only [Bool.or_eq_true] at checkedChild
  rcases checkedChild with here|no
  · exact Bool.false_ne_true ((hit_false proved here).symm.trans tail)
  · exact Bool.false_ne_true ((closed_false no).symm.trans tail)

def batch (f : Nat → Bool) (s : Nat) : Nat → Bool
  | 0 => true
  | n+1 => f (s+n) && batch f s n

theorem batch_mem {f : Nat→Bool} {start n} (h : batch f start n=true)
    (i : Nat) (lo : start ≤ i) (hi : i < start+n) : f i=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [batch,Bool.and_eq_true] at h
    by_cases eq : i=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem merge {f : Nat→Bool} {s a b} (h1 : batch f s a=true) (h2 : batch f (s+a) b=true) :
    batch f s (a+b)=true := by
  induction b with
  | zero => simpa using h1
  | succ b ih =>
    simp only [batch,Bool.and_eq_true] at h2
    simp only [Nat.add_succ,batch,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h2.1,ih h2.2⟩

theorem layer {guard g k next curr} (old : valid guard g k next)
    (checked : batch (fun i => node guard g k next (curr.state i)) 0 curr.size=true) : valid guard g (k+1) curr := by
  intro i hi
  exact node_false old (batch_mem (start:=0) checked i (Nat.zero_le i) (by simpa using hi))

theorem grouped {guard g k next curr} {groups block : Nat} (old : valid guard g k next)
    (positive : 0<block) (enough : curr.size≤groups*block)
    (checked : ∀ b : Fin groups, batch (fun i => node guard g k next (curr.state i))
      (b.val*block) block=true) : valid guard g (k+1) curr := by
  intro i hi
  have ib : i<groups*block := lt_of_lt_of_le hi enough
  have ib' : i/block<groups := (Nat.div_lt_iff_lt_mul positive).mpr ib
  let b : Fin groups := ⟨i/block,ib'⟩
  apply node_false old
  apply batch_mem (checked b)
  · exact Nat.div_mul_le_self i block
  · change i<(i/block)*block+block
    have md := Nat.mod_lt i positive
    have eq := Nat.mod_add_div i block
    rw [Nat.mul_comm block (i/block)] at eq
    omega

def blank : Table := ⟨0,fun _ => ⟨[],0⟩,fun _ => 0⟩

theorem blank_valid (guard : Nat → State → Bool) (g : Geometry) (k : Nat) : valid guard g k blank := by
  intro i hi
  exact (Nat.not_lt_zero _ hi).elim

end CoNine3024.Canon
