import PEqualNP.Co4358Cone

namespace CoNum4358
open CoAO3143

private theorem zero_l (d : Bool) (w : Sig) : bin d zero w = zero ∨ bin d zero w=w := by
  rcases w with ⟨x,y⟩
  cases d <;> simp [CoAO3143.bin,zero]
private theorem zero_r (d : Bool) (w : Sig) : bin d w zero = zero ∨ bin d w zero=w := by
  rcases w with ⟨x,y⟩
  cases d <;> simp [CoAO3143.bin,zero]
private theorem idem (d : Bool) (w : Sig) : bin d w w = w := by
  rcases w with ⟨x,y⟩
  cases d <;> simp [CoAO3143.bin]

private theorem bad_read (ws : List Sig) (i : Nat) (bad : ws.length≤i) :
    lookupKW ws i = zero := by
  simp [lookupKW,List.getD_eq_getElem?_getD,List.getElem?_eq_none bad]

theorem sane_of_fresh {ws : List Sig} {g : Gate} (fresh : ¬OK ws (g.kw ws)) :
    g.sane ws.length := by
  constructor
  · by_contra! h
    rcases zero_l g.isOr (lookupKW ws g.b) with e|e
    · exact fresh (Or.inl (by simpa only [Gate.kw,bad_read ws g.a h] using e))
    · have eq : g.kw ws = lookupKW ws g.b := by simpa only [Gate.kw,bad_read ws g.a h] using e
      exact fresh (eq ▸ lookup_ok ws g.b)
  constructor
  · by_contra! h
    rcases zero_r g.isOr (lookupKW ws g.a) with e|e
    · exact fresh (Or.inl (by simpa only [Gate.kw,bad_read ws g.b h] using e))
    · have eq : g.kw ws = lookupKW ws g.a := by simpa only [Gate.kw,bad_read ws g.b h] using e
      exact fresh (eq ▸ lookup_ok ws g.a)
  · intro same
    have eq : g.kw ws = lookupKW ws g.b := by simp only [Gate.kw,same,idem]
    exact fresh (eq ▸ lookup_ok ws g.b)

def Clean (ws : List Sig) : List Gate → Prop
  | [] => True
  | g::gs => g.sane ws.length ∧ ¬OK ws (g.kw ws) ∧ Clean (ws++[g.kw ws]) gs

theorem all_clean {ws : List Sig} {gs : List Gate} {out : Nat}
    (p : Price ws gs.length) (hit : lookupKW (bankKW ws gs) out=CoAO3143.target) :
    Clean ws gs := by
  induction gs generalizing ws with
  | nil => trivial
  | cons g gs ih =>
    have f := fresh_gate p hit
    exact ⟨sane_of_fresh f,f,ih (tail_price p g) hit⟩

private theorem count_cons {off out : Nat} {g : Gate} {gs : List Gate}
    (h : liveCount off out (g::gs)=(g::gs).length) :
    off∈need (off+1) out gs ∧ liveCount (off+1) out gs=gs.length := by
  have le := count_le (off+1) out gs
  simp only [liveCount,List.length_cons] at h
  split at h <;> rename_i e
  · exact ⟨e,by omega⟩
  · omega

theorem last_output (off out : Nat) (g : Gate) (gs : List Gate)
    (all : liveCount off out (g::gs)=(g::gs).length) : out=off+gs.length := by
  induction gs generalizing off g with
  | nil =>
    have m := (count_cons all).1
    simpa only [need,Finset.mem_singleton,List.length_nil,Nat.add_zero,eq_comm] using m
  | cons u us ih =>
    have e := ih (off+1) u (count_cons all).2
    simp only [List.length_cons]
    omega

theorem to_trail (ws : List Sig) (gs : List Gate) (out : Nat)
    (valid : Clean ws gs) (live : liveCount ws.length out gs=gs.length)
    (last : out=ws.length+gs.length-1) : DirTrail ws.length gs (need ws.length out gs) := by
  induction gs generalizing ws with
  | nil =>
    have e : out=ws.length-1 := by simpa using last
    simpa only [need,e] using (DirTrail.done (off:=ws.length))
  | cons g gs ih =>
    have used : ws.length∈(need (ws.length+1) out gs) := (count_cons live).1
    have len : (ws++[g.kw ws]).length=ws.length+1 := by simp
    have tail := ih (ws++[g.kw ws]) valid.2.2 (by rw [len]; exact (count_cons live).2)
      (by rw [len]; change out=ws.length+(g::gs).length-1 at last; simp only [List.length_cons] at last; omega)
    rw [len] at tail
    change DirTrail (ws.length+1) gs (need (ws.length+1) out gs) at tail
    have split : insert ws.length ((need (ws.length+1) out gs).erase ws.length)=(need (ws.length+1) out gs) := Finset.insert_erase used
    have tr := DirTrail.step (U:=(need (ws.length+1) out gs).erase ws.length) g valid.1 (Finset.notMem_erase _ _) (split.symm ▸ tail)
    simpa only [need,if_pos used] using tr

theorem need_bounded (ws : List Sig) (gs : List Gate) (out : Nat) (valid : Clean ws gs)
    (cap : out<ws.length+gs.length) : ∀ i∈need ws.length out gs, i<ws.length := by
  induction gs generalizing ws with
  | nil => simpa [need] using cap
  | cons g gs ih =>
    have len : (ws++[g.kw ws]).length=ws.length+1 := by simp
    have b := ih (ws++[g.kw ws]) valid.2.2 (by rw [len]; simp only [List.length_cons] at cap; omega)
    rw [len] at b
    intro i h
    simp only [need] at h
    split at h <;> rename_i use
    · simp only [Finset.mem_insert,Finset.mem_erase] at h
      rcases h with rfl|rfl|⟨ne,m⟩
      · exact valid.1.1
      · exact valid.1.2.1
      · have := b _ m; omega
    · have := b _ h
      have ne : i≠ws.length := fun eq => use (eq ▸ h)
      omega

#print axioms to_trail
end CoNum4358
