import Mathlib

namespace Co5339Fiber
abbrev Side (N : ℕ) := Fin N → Bool
abbrev Input (N : ℕ) := Side N × Side N
def allOnes (N : ℕ) : Side N := fun _ => true
def atom {N} (i : Fin N) : Side N := fun r => decide (r=i)
def Praw {N} (i : Fin N) : Set (Input N) := {v | v.1 i=true}
def Lraw {N} (i : Fin N) : Set (Input N) := {v | v.2 i=true}

def Prefix (N q : ℕ) : Set (Input N) := {v | ∀i : Fin N,i.val≤q → v.2 i=true}

def raiseInputs (N q : ℕ) (z : Input N) : Input N :=
  (fun i => z.1 i || decide (∀j : Fin N,j.val≤q → z.2 j=true),z.2)

theorem sparse_not_prefix {N q} (fits : q<N) {x y : Side N}
    (hy : Fintype.card {j // y j=true} ≤q) : (x,y)∉Prefix N q := by
  intro yes
  let lift : Fin (q+1) → {j // y j=true} := fun i => ⟨⟨i.val,by omega⟩,yes _ (by omega)⟩
  have inj : Function.Injective lift := by
    intro a b eq
    exact Fin.ext (congrArg (fun t : {j // y j=true} => t.val.val) eq)
  have bound := Fintype.card_le_of_injective lift inj
  simp only [Fintype.card_fin] at bound
  omega

theorem sparse_raise {N q} (fits : q<N) (x y : Side N)
    (hy : Fintype.card {j // y j=true} ≤q) : raiseInputs N q (x,y)=(x,y) := by
  have empty := sparse_not_prefix (x:=x) fits hy
  change ¬(∀i : Fin N,i.val≤q → y i=true) at empty
  simp [raiseInputs,empty]

theorem full_raise {N q} (x : Side N) : raiseInputs N q (x,allOnes N)=(allOnes N,allOnes N) := by
  simp [raiseInputs,allOnes]

def topGood {N} (S : Set (Input N)) := S=∅ ∨ (allOnes N,allOnes N)∈S
def fiberGood {N} (S : Set (Input N)) := S=∅ ∨ ∀x,(x,allOnes N)∈S

theorem full_preimage {N q} {S : Set (Input N)} (h : topGood S) :
    fiberGood (raiseInputs N q ⁻¹' S) := by
  rcases h with rfl|hit
  · left; rfl
  · right; intro x; change raiseInputs N q (x,allOnes N)∈S; rwa [full_raise]

theorem fiber_no_clean {N} (S out : Set (Input N)) (all : fiberGood S) (inside : S⊆out)
    (P L : Set (Side N)) (rect : S=P ×ˢ L) (p l : Fin N) (neg : Side N)
    (rejected : (neg,atom l)∉out) : (atom p,atom l)∉S := by
  intro hit
  rcases all with empty|univrow
  · rw [empty] at hit; exact hit
  · have full := univrow neg
    rw [rect] at full hit
    apply rejected
    apply inside
    rw [rect]
    exact ⟨full.1,hit.2⟩

theorem top_union {N} {S T : Set (Input N)} (a : topGood S) (b : topGood T) : topGood (S∪T) := by
  rcases a with rfl|ha
  · simpa using b
  · exact Or.inr (Or.inl ha)

theorem top_inter {N} {S T : Set (Input N)} (a : topGood S) (b : topGood T) : topGood (S∩T) := by
  rcases a with rfl|ha
  · left; simp
  rcases b with rfl|hb
  · left; simp
  · exact Or.inr ⟨ha,hb⟩

def Bases {N} (W : ℕ → Set (Input N)) := ∀i : Fin N,W i.val=Praw i ∧ W (N+i.val)=Lraw i

def LegalAt {N} (W : ℕ → Set (Input N)) (j : ℕ) :=
  ∃a b,max a b<j ∧ W j∈[W a∪W b,W a,∅,W a∩W b]

theorem available_top {N s} {W : ℕ → Set (Input N)} (base : Bases W)
    (gates : ∀i<s,LegalAt W (N+N+i)) : ∀j<N+N+s,topGood (W j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro bound
    by_cases pt : j<N
    · rw [(base ⟨j,pt⟩).1]; exact Or.inr rfl
    by_cases ln : j<N+N
    · let i : Fin N := ⟨j-N,by omega⟩
      have h : N+i.val=j := by dsimp [i]; omega
      rw [←h,(base i).2]; exact Or.inr rfl
    let g := j-(N+N)
    have eq : N+N+g=j := by dsimp [g]; omega
    obtain ⟨a,b,lt,op⟩ := gates g (by dsimp [g]; omega)
    rw [eq] at lt op
    have ha := ih a (by omega) (by omega)
    have hb := ih b (by omega) (by omega)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at op
    rcases op with hu|hc|he|hi
    · rw [hu]; exact top_union ha hb
    · rwa [hc]
    · rw [he]; exact Or.inl rfl
    · rw [hi]; exact top_inter ha hb

end Co5339Fiber
