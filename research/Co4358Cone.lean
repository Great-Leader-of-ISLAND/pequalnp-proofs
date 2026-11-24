import PEqualNP.Co4358Trail

namespace CoNum4358
open CoAO3143

/-- The two constants are available in a relaxed lower-bound problem. -/
def OK (xs : List Sig) (a : Sig) := a = zero ∨ a = one ∨ a ∈ xs

inductive Run (roots : List Sig) : Nat → List Sig → Prop
  | start : Run roots 0 roots
  | add {k bank a b} (pre : Run roots k bank) (d : Bool)
      (ha : OK bank a) (hb : OK bank b) :
      Run roots (k+1) (bin d a b :: bank)

def Price (xs : List Sig) (n : Nat) := ∀ k ys, Run xs k ys → OK ys CoAO3143.target → n ≤ k

private theorem old {ws : List Sig} {w : Sig} (a : Sig) (hw : OK ws w) : OK (a::ws) w := by
  rcases hw with eq|eq|mem
  · exact Or.inl eq
  · exact Or.inr (Or.inl eq)
  · exact Or.inr (Or.inr (List.mem_cons_of_mem _ mem))

private theorem from_mem {as bs : List Sig} (h : ∀ x ∈ as, OK bs x) :
    ∀ x, OK as x → OK bs x := by
  intro x hx
  rcases hx with eq|eq|mem
  · exact Or.inl eq
  · exact Or.inr (Or.inl eq)
  · exact h x mem

theorem lookup_ok (ws : List Sig) (i : Nat) : OK ws (lookupKW ws i) := by
  simp only [lookupKW,List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact Or.inl rfl
  | some w => exact Or.inr (Or.inr (List.mem_of_getElem? e))

private theorem lookup_append_eq (ws : List Sig) (w : Sig) :
    lookupKW (ws++[w]) ws.length = w := by
  simp [lookupKW,List.getD_eq_getElem?_getD]

private theorem lookup_append_ne (ws : List Sig) (w : Sig) (i : Nat) (ne : i ≠ ws.length) :
    lookupKW (ws++[w]) i = lookupKW ws i := by
  by_cases less : i < ws.length
  · simp [lookupKW,List.getD_eq_getElem?_getD,List.getElem?_append,less]
  · have gt : ws.length + 1 ≤ i := by omega
    have past : (ws++[w]).length ≤ i := by simpa using gt
    simp [lookupKW,List.getD_eq_getElem?_getD,List.getElem?_eq_none past,
      List.getElem?_eq_none (Nat.le_of_not_gt less)]

theorem continue_run {roots xs : List Sig} {k} (pre : Run roots k xs)
    (ws : List Sig) (known : ∀ x ∈ ws, OK xs x) (gs : List Gate) :
    ∃ ys, Run roots (k+gs.length) ys ∧ ∀ x ∈ bankKW ws gs, OK ys x := by
  induction gs generalizing xs ws k with
  | nil => exact ⟨xs,by simpa using pre,known⟩
  | cons g gs ih =>
    have a := from_mem known _ (lookup_ok ws g.a)
    have b := from_mem known _ (lookup_ok ws g.b)
    have run := Run.add pre g.isOr a b
    change Run roots (k+1) (g.kw ws::xs) at run
    have all (x) (hx : x ∈ ws++[g.kw ws]) : OK (g.kw ws::xs) x := by
      rcases List.mem_append.mp hx with before|last
      · exact old _ (known _ before)
      · exact Or.inr (Or.inr (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp last))))
    obtain ⟨ys,h,mem⟩ := ih run (ws++[g.kw ws]) all
    exact ⟨ys,by simpa only [List.length_cons,Nat.add_right_comm,Nat.add_assoc,
      Nat.add_comm] using h,mem⟩

theorem replay {ws xs : List Sig} {k} (run : Run ws k xs) {roots base : List Sig} {n}
    (pre : Run roots n base) (known : ∀ x ∈ ws, OK base x) :
    ∃ ys, Run roots (n+k) ys ∧ ∀ x ∈ xs, OK ys x := by
  induction run with
  | start => exact ⟨_,by simpa using pre,known⟩
  | add _ d ha hb ih =>
    obtain ⟨ys,r,mem⟩ := ih
    refine ⟨_,by simpa only [Nat.add_assoc] using Run.add r d (from_mem mem _ ha) (from_mem mem _ hb),?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with eq|m
    · exact Or.inr (Or.inr (List.mem_cons.mpr (Or.inl eq)))
    · exact old _ (mem _ m)

theorem tail_price {ws : List Sig} {n : Nat} (p : Price ws (n+1)) (g : Gate) :
    Price (ws++[g.kw ws]) n := by
  intro k ys r out
  have base : Run ws 1 (g.kw ws::ws) :=
    Run.add Run.start g.isOr (lookup_ok ws g.a) (lookup_ok ws g.b)
  have known (x) (hx : x∈ws++[g.kw ws]) : OK (g.kw ws::ws) x := by
    rcases List.mem_append.mp hx with m|e
    · exact Or.inr (Or.inr (List.mem_cons_of_mem _ m))
    · exact Or.inr (Or.inr (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp e))))
  obtain ⟨zs,c,sub⟩ := replay r base known
  have := p _ zs c (from_mem sub _ out)
  omega

theorem fresh_gate {ws : List Sig} {g : Gate} {gs : List Gate} {out : Nat}
    (low : Price ws (gs.length+1)) (hit : lookupKW (bankKW (ws++[g.kw ws]) gs) out=CoAO3143.target) :
    ¬ OK ws (g.kw ws) := by
  intro bad
  have known (x) (hx : x∈ws++[g.kw ws]) : OK ws x := by
    rcases List.mem_append.mp hx with m|e
    · exact Or.inr (Or.inr m)
    · exact (List.mem_singleton.mp e) ▸ bad
  obtain ⟨ys,r,mem⟩ := continue_run (roots:=ws) Run.start _ known gs
  have h := from_mem mem _ (lookup_ok _ out)
  rw [hit] at h
  have := low _ ys r h
  omega

/-- The exact addresses needed before a gate, collected backwards. -/
def need (off out : Nat) : List Gate → Finset Nat
  | [] => {out}
  | g::gs =>
    let T := need (off+1) out gs
    if off∈T then insert g.a (insert g.b (T.erase off)) else T

def liveCount (off out : Nat) : List Gate → Nat
  | [] => 0
  | _::gs => liveCount (off+1) out gs + if off∈need (off+1) out gs then 1 else 0

theorem count_le (off out : Nat) (gs : List Gate) : liveCount off out gs ≤ gs.length := by
  induction gs generalizing off with
  | nil => simp [liveCount]
  | cons g gs ih =>
    have h := ih (off+1)
    simp only [liveCount,List.length_cons]
    split <;> omega

theorem cone_run {roots xs : List Sig} {k} (pre : Run roots k xs)
    (ws : List Sig) (gs : List Gate) (out : Nat)
    (known : ∀ i ∈ need ws.length out gs, OK xs (lookupKW ws i)) :
    ∃ ys, Run roots (k+liveCount ws.length out gs) ys ∧
      OK ys (lookupKW (bankKW ws gs) out) := by
  induction gs generalizing ws xs k with
  | nil => exact ⟨_,by simpa [liveCount] using pre,known _ (by simp [need])⟩
  | cons g gs ih =>
    let off := ws.length
    let T := need (off+1) out gs
    let next := ws++[g.kw ws]
    have len : next.length = off+1 := by simp [next,off]
    by_cases used : off∈T
    · have hknown : ∀ i ∈ insert g.a (insert g.b (T.erase off)), OK xs (lookupKW ws i) := by
        simpa only [need,if_pos used] using known
      have a := hknown g.a (Finset.mem_insert_self _ _)
      have b := hknown g.b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      have r : Run roots (k+1) (g.kw ws::xs) := Run.add pre g.isOr a b
      have keep (i) (hi : i∈need next.length out gs) : OK (g.kw ws::xs) (lookupKW next i) := by
        rw [len] at hi
        by_cases e : i=off
        · subst i
          rw [show lookupKW next off = g.kw ws from lookup_append_eq _ _]
          exact Or.inr (Or.inr List.mem_cons_self)
        · rw [show lookupKW next i = lookupKW ws i from lookup_append_ne _ _ i e]
          exact old _ (hknown _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨e,hi⟩))))
      obtain ⟨ys,rr,h⟩ := ih r next keep
      rw [len] at rr
      refine ⟨ys,?_,h⟩
      convert rr using 1 <;> simp only [liveCount,if_pos used] <;> omega
    · have keep (i) (hi : i∈need next.length out gs) : OK xs (lookupKW next i) := by
        rw [len] at hi
        have e : i≠off := fun eq => used (eq ▸ hi)
        rw [show lookupKW next i = lookupKW ws i from lookup_append_ne _ _ i e]
        apply known
        simpa only [need,if_neg used] using hi
      obtain ⟨ys,rr,h⟩ := ih pre next keep
      rw [len] at rr
      refine ⟨ys,?_,h⟩
      simpa only [liveCount,if_neg used,Nat.add_zero] using rr

theorem no_dead {ws : List Sig} {gs : List Gate} {out : Nat} (p : Price ws gs.length)
    (hit : lookupKW (bankKW ws gs) out = CoAO3143.target) : liveCount ws.length out gs = gs.length := by
  obtain ⟨ys,r,h⟩ := cone_run (roots:=ws) Run.start ws gs out (fun i _ => lookup_ok ws i)
  rw [hit] at h
  have := p _ ys r h
  have := count_le ws.length out gs
  omega

end CoNum4358
