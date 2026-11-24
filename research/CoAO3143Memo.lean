import PEqualNP.CoAO3143CotreeCheck
import PEqualNP.CoAO3143SevenData

namespace CoAO3143.Memo
open Cotree ProtocolProof

structure Table where
  count : Nat
  state : Nat → List Sig
  place : List Sig → Nat

def matched (T : Table) (xs : List Sig) : Bool :=
  let i := T.place xs
  decide (i<T.count) && xs.isPerm (T.state i)

def Valid (T : Table) (k : Nat) : Prop := ∀i<T.count, Impossible k 0 (T.state i)

private theorem equal_set {a b : List Sig} (eq : a.Perm b) : a.toFinset=b.toFinset := by
  ext w
  simpa using eq.mem_iff (a:=w)

private theorem matched_ok {T : Table} {k xs} (v : Valid T k) (h : matched T xs=true) :
    Impossible k 0 xs := by
  unfold matched at h
  simp only [Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at h
  intro m hm run
  apply v _ h.1 m hm
  rwa [←equal_set h.2]

def blocked (grid : Grid) (k : Nat) (T : Table) (ws : List Sig) : Bool :=
  (ws.length==k+1 && cotreeReject grid ws) || matched T ws

private theorem blocked_ok {g k T ws} (valid : Valid T k) (hn : ws.Nodup)
    (h : blocked g k T ws=true) : Impossible k 0 ws := by
  simp only [blocked,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at h
  rcases h with ⟨len,bad⟩ | found
  · intro m cap hs
    have bd := ProtocolProof.width hs.live
    have size := List.toFinset_card_of_nodup hn
    have ok := cotree_false hs.live (by omega) g
    exact Bool.false_ne_true (ok.symm.trans bad)
  · exact matched_ok valid found

def node (g : Grid) (k : Nat) (T : Table) (ws : List Sig) : Bool :=
  decide ws.Nodup && !(stepTest k 0 ws (fun _ => true) (fun v => !(blocked g k T v)))

theorem node_ok {g k T ws} (valid : Valid T k) (h : node g k T ws=true) : Impossible (k+1) 0 ws := by
  simp only [node,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at h
  intro n cap run
  have contradiction := reduced_step run cap h.1 rfl (u:=fun _ => true)
    (b:=fun v => !(blocked g k T v)) (fun _ _ _ _ _ => rfl) (by
      intro v hn m hm hr
      cases eq : blocked g k T v with
      | false => rfl
      | true => exact (blocked_ok valid hn eq m hm hr).elim)
  exact Bool.false_ne_true (h.2.symm.trans contradiction)

def empty : Table := ⟨0,fun _ => [],fun _ => 0⟩
theorem empty_ok (k : Nat) : Valid empty k := by
  intro i hi
  exact (Nat.not_lt_zero _ hi).elim

/-- A finite union of checked ranges is used instead of evaluating the
    complete proof in one kernel reduction. -/
def allAt (p : Nat→Bool) (beginning : Nat) : Nat → Bool
  | 0 => true
  | size+1 => allAt p beginning size && p (beginning+size)

theorem allAt_get {p : Nat → Bool} {b n : Nat} (h : allAt p b n = true) (i : Nat)
    (lo : b ≤ i) (hi : i < b + n) : p i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    have checks := Bool.and_eq_true_iff.mp h
    by_cases l : i<b+n
    · exact ih checks.1 l
    · have e : i=b+n := by omega
      simpa [e] using checks.2

theorem allAt_join {p b m n} (a : allAt p b m=true) (c : allAt p (b+m) n=true) :
    allAt p b (m+n)=true := by
  induction n with
  | zero => simpa using a
  | succ n ih =>
    obtain ⟨l,r⟩ := Bool.and_eq_true_iff.mp c
    apply Bool.and_eq_true_iff.mpr
    exact ⟨ih l, by simpa [Nat.add_assoc] using r⟩

theorem layer_ok {g k next curr} (child : Valid next k)
    (h : allAt (fun i => node g k next (curr.state i)) 0 curr.count=true) : Valid curr (k+1) := by
  intro i hi
  apply node_ok (g := g) child
  exact allAt_get h i (by omega) (by simpa using hi)

theorem grouped_layer {g k next curr} (good : Valid next k) (chunk : Nat) (hc : 0<chunk)
    (groups : Nat) (cover : curr.count≤groups*8*chunk)
    (cert : ∀ a : Fin groups,∀ b : Fin 8,
      allAt (fun i => node g k next (curr.state i)) ((a.val*8+b.val)*chunk)
        (min chunk (curr.count-(a.val*8+b.val)*chunk))=true) : Valid curr (k+1) := by
  intro i hi
  apply node_ok (g := g) good
  have div : i/chunk < groups*8 := (Nat.div_lt_iff_lt_mul hc).2 (by omega)
  have div8 : i/chunk/8<groups := (Nat.div_lt_iff_lt_mul (by decide : 0<8)).2 (by simpa [Nat.mul_comm] using div)
  let a : Fin groups := ⟨i/chunk/8,div8⟩
  let b : Fin 8 := ⟨(i/chunk)%8,Nat.mod_lt _ (by decide)⟩
  have ab : a.val*8+b.val=i/chunk := by dsimp [a,b]; omega
  have h := cert a b
  rw [ab] at h
  apply allAt_get h i (Nat.div_mul_le_self _ _)
  have less := Nat.mod_lt i hc
  have eq := Nat.mod_add_div i chunk
  rw [Nat.mul_comm chunk (i/chunk)] at eq
  omega

end CoAO3143.Memo
