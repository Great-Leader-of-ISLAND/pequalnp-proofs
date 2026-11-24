import Mathlib

namespace PhaseTwo.CycleFork

variable {V : Type*} [DecidableEq V]
def edge (G : SimpleGraph V) (S : Finset V) : Prop := ∃ x ∈ S, ∃ y ∈ S, G.Adj x y

theorem singleton_off (G : SimpleGraph V) (b : V) : ¬edge G {b} := by
  rintro ⟨u,hu,v,hv,hadj⟩
  simp only [Finset.mem_singleton] at hu hv
  subst u
  subst v
  exact G.loopless.irrefl _ hadj

theorem pair_off (G : SimpleGraph V) (b u : V) (ind : ¬G.Adj b u) :
    ¬edge G {b,u} := by
  rintro ⟨w,hw,z,hz,hadj⟩
  simp only [Finset.mem_insert,Finset.mem_singleton] at hw hz
  rcases hw with rfl|rfl <;> rcases hz with rfl|rfl
  · exact G.loopless.irrefl _ hadj
  · exact ind hadj
  · exact ind hadj.symm
  · exact G.loopless.irrefl _ hadj

theorem or_distinguish (G : SimpleGraph V) {p b u v : V} (pb : p≠b)
    (pu : G.Adj p u) (pv : G.Adj p v) (uv : u≠v)
    (noFour : ∀ a b c d : V, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      G.Adj a b → G.Adj b c → G.Adj c d → ¬G.Adj d a) :
    ∃ S : Finset V, p ∉ S ∧ b ∈ S ∧ ¬edge G S ∧ edge G (insert p S) := by
  by_cases ab : G.Adj p b
  · exact ⟨{b},by simpa,Finset.mem_singleton_self _,singleton_off _ _,
      p,Finset.mem_insert_self _ _,b,Finset.mem_insert_of_mem (Finset.mem_singleton_self _),ab⟩
  have bu : b≠u := fun e => ab (e ▸ pu)
  have bv : b≠v := fun e => ab (e ▸ pv)
  have absent : ¬G.Adj b u ∨ ¬G.Adj b v := by
    by_contra! both
    exact noFour p u b v pu.ne pb pv.ne bu.symm uv bv pu both.1.symm both.2 pv.symm
  obtain ⟨w,aw,bw⟩ : ∃ w, G.Adj p w ∧ ¬G.Adj b w := by
    rcases absent with h|h
    · exact ⟨u,pu,h⟩
    · exact ⟨v,pv,h⟩
  refine ⟨{b,w},by simp [pb,aw.ne],Finset.mem_insert_self _ _,pair_off _ _ _ bw,?_⟩
  exact ⟨p,Finset.mem_insert_self _ _,w,by simp,aw⟩

theorem and_distinguish (G : SimpleGraph V) {p b u v : V} (pb : p≠b)
    (pu : G.Adj p u) (pv : G.Adj p v) (uv : u≠v) :
    ∃ S : Finset V, p ∉ S ∧ b ∉ insert p S ∧ ¬edge G S ∧ edge G (insert p S) := by
  obtain ⟨w,aw,bw⟩ : ∃ w, G.Adj p w ∧ b≠w := by
    by_cases h : b=u
    · exact ⟨v,pv,h ▸ uv⟩
    · exact ⟨u,pu,h⟩
  exact ⟨{w},by simp [aw.ne],by simp [pb.symm,bw],singleton_off _ _,
     p,Finset.mem_insert_self _ _,w,by simp,aw⟩

private theorem four {n : Nat} (L : Finset (Fin n)) {a b c d : Fin n}
    (ha : a∈L) (hb : b∈L) (hc : c∈L) (hd : d∈L)
    (ab : a≠b) (ac : a≠c) (ad : a≠d) (bc : b≠c) (bd : b≠d) (cd : c≠d) : 4≤L.card := by
  have sub : ({a,b,c,d} : Finset (Fin n)) ⊆ L := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl|rfl <;> assumption
  have card := Finset.card_le_card sub
  simpa [Finset.card_insert_of_notMem,ab,ac,ad,bc,bd,cd] using card

theorem double_constant_charge {n : Nat} (succs : Fin n → Finset (Fin n)) (L : Finset (Fin n))
    (forward : ∀ x y, y∈succs x → x<y) {a b : Fin n} (ab : a≠b)
    (aL : a∈L) (bL : b∈L) (noab : b∉succs a) (noba : a∉succs b)
    (aa : (succs a).Nonempty) (bb : (succs b).Nonempty)
    (la : succs a ⊆ L) (lb : succs b ⊆ L)
    (shared : ∀ t, t∈succs a → t∈succs b → ∃ d ∈ succs t, d∈L) : 4≤L.card := by
  obtain ⟨s,hs⟩ := aa
  obtain ⟨t,ht⟩ := bb
  have as := forward _ _ hs
  have bt := forward _ _ ht
  by_cases st : s=t
  · subst t
    obtain ⟨d,hd,hl⟩ := shared s hs ht
    have sd := forward _ _ hd
    exact four L aL bL (la hs) hl ab (ne_of_lt as) (ne_of_lt (lt_trans as sd))
      (ne_of_lt bt) (ne_of_lt (lt_trans bt sd)) (ne_of_lt sd)
  · exact four L aL bL (la hs) (lb ht) ab (ne_of_lt as)
      (fun e => noba (e ▸ ht)) (fun e => noab (e ▸ hs)) (ne_of_lt bt) st

end PhaseTwo.CycleFork
