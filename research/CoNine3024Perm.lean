import PEqualNP.CoNine3024Split

namespace CoNine3024.Reorder

def Rel (s t : State) := s.spent=t.spent ∧ s.wires.Perm t.wires

theorem symmetry {s t : State} (h : Rel s t) : Rel t s := ⟨h.1.symm,h.2.symm⟩

private theorem any_perm {as bs : List Atom} (h : as.Perm bs) (f : Atom → Bool) : as.any f=bs.any f := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp [ih]
  | swap a b t => simp only [List.any_cons]; ac_rfl
  | trans _ _ ha hb => exact ha.trans hb

private theorem cost_perm {as bs : List Atom} (h : as.Perm bs) (n : Nat) :
    as.foldl (fun k a => k+a.fixed) n=bs.foldl (fun k a => k+a.fixed) n := by
  induction h generalizing n with
  | nil => rfl
  | cons a _ ih => exact ih _
  | swap a b t => simp only [List.foldl_cons]; congr 1 <;> omega
  | trans _ _ ha hb => exact (ha n).trans (hb n)

private theorem cov_perm {as bs : List Atom} (h : as.Perm bs) (v : Cells) :
    as.foldl (fun z a => z ||| separator a) v=bs.foldl (fun z a => z ||| separator a) v := by
  induction h generalizing v with
  | nil => rfl
  | cons a _ ih => exact ih _
  | swap a b t => simp only [List.foldl_cons]; congr 1 <;> ac_rfl
  | trans _ _ ha hb => exact (ha v).trans (hb v)

theorem safe_eq {s t : State} (h : Rel s t) : safe s=safe t := by
  unfold safe
  rw [h.1,cost_perm h.2]

theorem cover_eq {g : Geometry} {s t : State} (h : Rel s t) : covered g s.wires=covered g t.wires := by
  unfold covered
  rw [cov_perm h.2]

private theorem live_iff (g : Geometry) (s : State) : live g s =
    ((s.wires.length==1) && s.wires.any (fun a => a.full==g.target)) := by
  rcases s with ⟨ws,n⟩
  cases ws with
  | nil => rfl
  | cons a xs => cases xs with
    | nil => simp [live]
    | cons b xs => simp [live]

theorem live_eq {g : Geometry} {s t : State} (h : Rel s t) : live g s=live g t := by
  rw [live_iff,live_iff,h.2.length_eq,any_perm h.2]

private theorem op_comm (g : Geometry) (d : Bool) (a b : Atom) : operation g d a b=operation g d b a := by
  cases d <;> simp [operation,BitVec.and_comm,BitVec.or_comm]

def reversed : Nat → Nat | 1 => 2 | 2 => 1 | n => n

private theorem rev_mem {m : Nat} (h : m∈([0,1,2,3] : List Nat)) : reversed m∈([0,1,2,3] : List Nat) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl <;> decide

private theorem flipKeep (a b : Atom) {m : Nat} (h : m∈([0,1,2,3] : List Nat)) :
    (maskKeep a b m).Perm (maskKeep b a (reversed m)) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl
  · exact .refl _
  · exact .refl _
  · exact .refl _
  · exact .swap _ _ []

private theorem rest_perm {s t : State} (h : Rel s t) (a b : Atom) : (rest s a b).Perm (rest t a b) :=
  h.2.filter _

private theorem rest_flip (s : State) (a b : Atom) : rest s b a=rest s a b := by
  unfold rest
  simp only [Bool.and_comm]

private theorem next_rel {s t : State} (h : Rel s t) {a b c d z : Atom} {m n : Nat}
    (charges : a.fixed ||| b.fixed=c.fixed ||| d.fixed)
    (tails : (rest s a b).Perm (rest t c d)) (keep : (maskKeep a b m).Perm (maskKeep c d n)) :
    Rel (child s a b z (rest s a b) m) (child t c d z (rest t c d) n) := by
  exact ⟨by simp [child,h.1,charges], .cons z (keep.append tails)⟩

private theorem pair_atoms {a b : Atom} {ws : List Atom} (e : (a,b)∈pairs ws) : a∈ws ∧ b∈ws := by
  induction ws with
  | nil => simp [pairs] at e
  | cons x xs ih =>
    rcases List.mem_append.mp e with here|there
    · obtain ⟨y,hy,eq⟩ := List.mem_map.mp here
      cases eq
      exact ⟨List.mem_cons_self,List.mem_cons_of_mem _ hy⟩
    · have m := ih there
      exact ⟨List.mem_cons_of_mem _ m.1,List.mem_cons_of_mem _ m.2⟩

private theorem valid_choice {g k s a b d u} (hu : u∈choices g k s a b d) :
    let z := operation g d a b
    (z.full==0 || z.full==BitVec.allOnes 512 || s.wires.any (fun w => w.full==z.full))=false ∧
    ∃ m ∈ ([0,1,2,3] : List Nat), u=child s a b z (rest s a b) m ∧
      u.wires.length≤k+1 ∧ safe u=true ∧ covered g u.wires=true := by
  dsimp only
  unfold choices at hu
  dsimp only at hu
  split at hu
  · simp at hu
  · rename_i nb
    refine ⟨Bool.eq_false_iff.mpr nb,?_⟩
    obtain ⟨m,hm,e⟩ := List.mem_filterMap.mp hu
    split at e
    · rename_i ok
      cases e
      exact ⟨m,hm,rfl,ok⟩
    · contradiction

private theorem children_of {g k s a b d u} (hpair : (a,b)∈pairs s.wires)
    (h : u∈choices g k s a b d) : u∈children g k s := by
  apply List.mem_flatMap.mpr
  refine ⟨(a,b),hpair,?_⟩
  cases d with
  | false => exact List.mem_append_left _ h
  | true => exact List.mem_append_right _ h

private theorem children_transfer {g k s t u} (h : Rel s t) (hu : u∈children g k s) :
    ∃ v∈children g k t, Rel u v := by
  obtain ⟨⟨a,b⟩,pair,hm⟩ := List.mem_flatMap.mp hu
  have dec : ∃ d, u∈choices g k s a b d := by
    rcases List.mem_append.mp hm with c|c
    · exact ⟨false,c⟩
    · exact ⟨true,c⟩
  obtain ⟨d,c⟩ := dec
  obtain ⟨good,m,hm,rfl,wid,budget,cov⟩ := valid_choice c
  let z := operation g d a b
  change (z.full==0 || z.full==BitVec.allOnes 512 || s.wires.any (fun w => w.full==z.full))=false at good
  have info : z.full≠0 ∧ z.full≠BitVec.allOnes 512 ∧ ∀w∈s.wires,w.full≠z.full := by
    by_contra! bad
    have fals : (z.full==0 || z.full==BitVec.allOnes 512 || s.wires.any (fun w => w.full==z.full))=true := by
      simp only [Bool.or_eq_true,beq_iff_eq,List.any_eq_true]
      tauto
    exact Bool.false_ne_true (good.symm.trans fals)
  have ab := pair_atoms pair
  have n : a≠b := by
    intro e
    subst b
    have q : z.full=a.full := by cases d <;> simp [z,operation]
    exact info.2.2 a ab.1 q.symm
  have available := pair_or (h.2.mem_iff.mp ab.1) (h.2.mem_iff.mp ab.2) n
  have small : m<4 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hm; omega
  have fresh (w) (hw : w∈t.wires) : w.full≠z.full := info.2.2 w (h.2.mem_iff.mpr hw)
  rcases available with same|rev
  · have rel := next_rel (z:=z) (m:=m) h (a:=a) (b:=b) (c:=a) (d:=b) rfl (rest_perm h _ _) (.refl _)
    refine ⟨_, child_mem g k t a b d m same small info.1 info.2.1 fresh ?_ ?_ ?_, rel⟩
    · rwa [←rel.2.length_eq]
    · rwa [←safe_eq rel]
    · rwa [←cover_eq rel]
  · have revS : reversed m<4 := by
      have p := rev_mem hm
      simp only [List.mem_cons,List.not_mem_nil,or_false] at p
      omega
    have tails : (rest s a b).Perm (rest t b a) := by rw [rest_flip]; exact rest_perm h _ _
    have rel := next_rel (z:=z) h (a:=a) (b:=b) (c:=b) (d:=a) (by exact Nat.or_comm _ _) tails (flipKeep a b hm)
    let v := child t b a z (rest t b a) (reversed m)
    refine ⟨v,?_,rel⟩
    change child t b a (operation g d a b) (rest t b a) (reversed m)∈children g k t
    rw [op_comm g d a b]
    apply child_mem g k t b a d (reversed m) rev revS
    · simpa [←op_comm g d a b] using info.1
    · simpa [←op_comm g d a b] using info.2.1
    · simpa [←op_comm g d a b] using fresh
    · simpa only [←op_comm g d a b,←rel.2.length_eq] using wid
    · simpa only [←op_comm g d a b,←safe_eq rel] using budget
    · simpa only [←op_comm g d a b,←cover_eq rel] using cov

/-- Genuine proofs at one canonical representative apply to every ordering of
    that same complete frontier, including all nine accumulated charges. -/
theorem search_forward (g : Geometry) (k : Nat) {s t} (rel : Rel s t) (yes : search g k s=true) : search g k t=true := by
  induction k generalizing s t with
  | zero => exact (live_eq rel).symm.trans yes
  | succ n ih =>
    simp only [search,Bool.or_eq_true,Bool.and_eq_true] at yes ⊢
    rcases yes with found|⟨safe,move⟩
    · exact Or.inl ((live_eq rel).symm.trans found)
    · obtain ⟨u,step,tail⟩ := List.any_eq_true.mp move
      obtain ⟨v,ok,h⟩ := children_transfer rel step
      exact Or.inr ⟨(safe_eq rel).symm.trans safe,List.any_eq_true.mpr ⟨v,ok,ih h tail⟩⟩

end CoNine3024.Reorder
