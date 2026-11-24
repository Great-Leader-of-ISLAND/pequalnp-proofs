import PEqualNP.Co5339Fiber

namespace Co5339Fiber

def guardSlot (N j : ℕ) := if j=0 then N else N+N+(j-1)
def slot (N q j : ℕ) := if j<N then N+N+q+j else if j<N+N then j else j+q+N

def padded {N} (q : ℕ) (W : ℕ → Set (Input N)) (j : ℕ) : Set (Input N) :=
  if j<N+N then W j else if j<N+N+q then Prefix N (j-(N+N)+1)
  else if j<N+N+q+N then W (j-(N+N+q)) ∪ Prefix N q
  else raiseInputs N q ⁻¹' W (j-(N+q))

theorem pad_base {N q} {W : ℕ → Set (Input N)} (base : Bases W) : Bases (padded q W) := by
  intro p
  have a : p.val<N+N := by omega
  have b : N+p.val<N+N := by omega
  simpa only [padded,if_pos a,if_pos b] using base p

theorem pre_point {N q} (i : Fin N) : raiseInputs N q ⁻¹' Praw i = Praw i ∪ Prefix N q := by
  ext z
  simp only [Set.mem_preimage,Praw,Set.mem_setOf_eq,raiseInputs,Set.mem_union,Prefix,Bool.or_eq_true,decide_eq_true_eq]

theorem pad_slot {N q} {W : ℕ → Set (Input N)} (base : Bases W) (j : ℕ) :
    padded q W (slot N q j)=raiseInputs N q ⁻¹' W j := by
  by_cases pt : j<N
  · have h0 : ¬N+N+q+j<N+N := by omega
    have h1 : ¬N+N+q+j<N+N+q := by omega
    have h2 : N+N+q+j<N+N+q+N := by omega
    have sub : N+N+q+j-(N+N+q)=j := by omega
    simp only [slot,if_pos pt,padded,if_neg h0,if_neg h1,if_pos h2,sub]
    rw [(base ⟨j,pt⟩).1,pre_point]
  by_cases ln : j<N+N
  · simp only [slot,if_neg pt,if_pos ln,padded]
    let l : Fin N := ⟨j-N,by omega⟩
    have eq : N+l.val=j := by dsimp [l]; omega
    rw [←eq,(base l).2]; rfl
  · have h0 : ¬j+q+N<N+N := by omega
    have h1 : ¬j+q+N<N+N+q := by omega
    have h2 : ¬j+q+N<N+N+q+N := by omega
    have sub : j+q+N-(N+q)=j := by omega
    simp only [slot,if_neg pt,if_neg ln,padded,if_neg h0,if_neg h1,if_neg h2,sub]

theorem prefix_zero {N} (pos : 0<N) : Prefix N 0=Lraw ⟨0,pos⟩ := by
  ext z
  constructor
  · intro h; exact h ⟨0,pos⟩ (by simp)
  · intro h i hi
    have eq : i=⟨0,pos⟩ := Fin.ext (by omega)
    simpa only [eq] using h

theorem prefix_next {N} (j : ℕ) (fit : j+1<N) :
    Prefix N (j+1)=Prefix N j ∩ Lraw ⟨j+1,fit⟩ := by
  ext z
  constructor
  · intro h; exact ⟨fun i hi => h i (by omega),h _ (by simp)⟩
  · rintro ⟨before,last⟩ i hi
    by_cases early : i.val≤j
    · exact before i early
    · have eq : i=⟨j+1,fit⟩ := Fin.ext (by omega)
      simpa only [eq] using last

theorem pad_guard {N q} {W : ℕ → Set (Input N)} (base : Bases W) (fits : q<N) {j} (bound : j≤q) :
    padded q W (guardSlot N j)=Prefix N j := by
  cases j with
  | zero =>
    have lt : N<N+N := by omega
    have pos : 0<N := by omega
    have base0 := (base ⟨0,pos⟩).2
    simpa [guardSlot,padded,lt,prefix_zero pos] using base0
  | succ j =>
    have h0 : ¬N+N+j<N+N := by omega
    have h1 : N+N+j<N+N+q := by omega
    have sub : N+N+j-(N+N)=j := by omega
    simp only [guardSlot,Nat.succ_ne_zero,if_false,Nat.succ_sub_one,padded,if_neg h0,if_pos h1,sub]

theorem slot_lt {N q t j} (hn : 0<N) (tr : t<N+N+j) : slot N q t<N+N+q+N+j := by
  unfold slot; split <;> try split <;> omega

theorem pad_gate {N s q} {W : ℕ → Set (Input N)} (fits : q<N) (base : Bases W)
    (old : ∀i<s,LegalAt W (N+N+i)) :
    ∀h<q+N+s,LegalAt (padded q W) (N+N+h) := by
  intro h bound
  by_cases gh : h<q
  · let l : Fin N := ⟨h+1,by omega⟩
    have lhs : N+N+h=guardSlot N (h+1) := by simp [guardSlot]
    have before : guardSlot N h < N+N+h := by unfold guardSlot; split <;> omega
    have right : N+l.val < N+N+h := by dsimp [l]; omega
    refine ⟨guardSlot N h,N+l.val,by omega,?_⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false]; right; right; right
    rw [lhs,pad_guard base fits (by omega),pad_guard base fits (by omega),(pad_base base l).2]
    exact prefix_next h l.isLt
  by_cases pt : h<q+N
  · let p : Fin N := ⟨h-q,by omega⟩
    have lhs : N+N+h=slot N q p.val := by simp only [slot,if_pos p.isLt]; dsimp [p]; omega
    have before : guardSlot N q<N+N+h := by unfold guardSlot; split <;> omega
    refine ⟨p.val,guardSlot N q,by have := p.isLt; omega,?_⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false]; left
    rw [lhs,pad_slot base,(base p).1,pre_point,(pad_base base p).1,pad_guard base fits le_rfl]
  · let j := h-(q+N)
    have eq : q+N+j=h := by dsimp [j]; omega
    have lj : j<s := by omega
    let v := N+N+j
    have hs : N+N+h=slot N q v := by
      have a : ¬v<N := by dsimp [v]; omega
      have b : ¬v<N+N := by dsimp [v]; omega
      rw [slot,if_neg a,if_neg b]; dsimp [v]; omega
    obtain ⟨a,b,lt,op⟩ := old j lj
    have la := slot_lt (q:=q) (N:=N) (j:=j) (t:=a) (by omega) (by omega)
    have lb := slot_lt (q:=q) (N:=N) (j:=j) (t:=b) (by omega) (by omega)
    refine ⟨slot N q a,slot N q b,by omega,?_⟩
    rw [hs,pad_slot base,pad_slot base,pad_slot base]
    change raiseInputs N q ⁻¹' W (N+N+j) ∈ _
    simp only [List.mem_cons,List.not_mem_nil,or_false] at op ⊢
    rcases op with hu|hc|he|hi
    · left; rw [hu]; rfl
    · right; left; rw [hc]
    · right; right; left; rw [he]; rfl
    · right; right; right; rw [hi]; rfl

theorem pad_gate_fiber {N s q} {W : ℕ → Set (Input N)} (fits : q<N) (base : Bases W)
    (old : ∀i<s,LegalAt W (N+N+i)) {h} (bound : h<q+N+s) : fiberGood (padded q W (N+N+h)) := by
  by_cases gh : h<q
  · have lhs : N+N+h=guardSlot N (h+1) := by simp [guardSlot]
    rw [lhs,pad_guard base fits (by omega)]
    right; intro x i hi; rfl
  by_cases pt : h<q+N
  · let p : Fin N := ⟨h-q,by omega⟩
    have lhs : N+N+h=slot N q p.val := by simp only [slot,if_pos p.isLt]; dsimp [p]; omega
    rw [lhs,pad_slot base,(base p).1]
    exact full_preimage (Or.inr rfl)
  · let j := h-(q+N)
    have eq : q+N+j=h := by dsimp [j]; omega
    have a : ¬N+N+j<N := by omega
    have b : ¬N+N+j<N+N := by omega
    have lhs : N+N+h=slot N q (N+N+j) := by rw [slot,if_neg a,if_neg b]; omega
    rw [lhs,pad_slot base]
    exact full_preimage (available_top base old _ (by omega))

end Co5339Fiber
