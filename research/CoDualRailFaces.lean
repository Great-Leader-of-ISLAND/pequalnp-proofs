import PEqualNP.CoCofactor29
namespace CoCofactor29

def setZero (x : Row) (b : Bool) (i : Fin 9) := if i=0 then b else x i
def ordered (x y : Row) := ∀ i, x i=true → y i=true

theorem setZero_mono (x : Row) : ordered (setZero x false) (setZero x true) := by
  intro i
  by_cases h : i=0 <;> simp [setZero,h]

theorem self_zero (x : Row) : setZero x (x 0)=x := by
  funext i
  by_cases e : i=0 <;> simp [setZero,e]

theorem constants_need_both_faces (H : Row → Bool → Bool)
    (mono : ∀ x y p q, ordered x y → (p=true → q=true) → H x p=true → H y q=true)
    (agrees : ∀ x, H x (!(x 0))=target x)
    (noConst : ∀ b, (fun x => H x b) ≠ target) :
    (∃ r∈rows, (bitRow r) 0=false ∧ target (bitRow r)=true ∧
      ∀ a b, H (setZero (bitRow r) a) b = (a || b)) ∧
    (∃ r∈rows, (bitRow r) 0=true ∧ target (bitRow r)=false ∧
      ∀ a b, H (setZero (bitRow r) a) b = (a && b)) := by
  classical
  have bad (b : Bool) : ∃ r∈rows, H (bitRow r) b ≠ target (bitRow r) := by
    by_contra! yes
    apply noConst b
    apply complete
    · intro x y xy
      exact mono x y b b (of_decide_eq_true (Bool.and_eq_true_iff.mp xy).2) id
    · exact yes
  have localMono (r : Nat) (a b c d : Bool) (ac : a=true → c=true) (bd : b=true → d=true) :
      H (setZero (bitRow r) a) b=true → H (setZero (bitRow r) c) d=true := by
    apply mono _ _ _ _ _ bd
    intro i
    by_cases z : i=0
    · simpa [setZero,z] using ac
    · simp [setZero,z]
  have truePair (r : Nat) : target (setZero (bitRow r) false)=true → target (setZero (bitRow r) true)=true := by
    intro h
    have step (a b : Fin 9) : (setZero (bitRow r) false a && setZero (bitRow r) false b)=true →
      (setZero (bitRow r) true a && setZero (bitRow r) true b)=true := by
      simp only [Bool.and_eq_true]
      rintro ⟨u,v⟩
      exact ⟨setZero_mono _ a u,setZero_mono _ b v⟩
    simp only [target,Bool.or_eq_true] at h ⊢
    grind
  have off (r : Nat) : H (setZero (bitRow r) false) true=target (setZero (bitRow r) false) := by
    simpa [setZero] using agrees (setZero (bitRow r) false)
  have on_ (r : Nat) : H (setZero (bitRow r) true) false=target (setZero (bitRow r) true) := by
    simpa [setZero] using agrees (setZero (bitRow r) true)
  constructor
  · obtain ⟨r,hr,bad⟩ := bad false
    cases z : bitRow r 0 with
    | true => exact (bad (by simpa [z] using agrees (bitRow r))).elim
    | false =>
      have self : setZero (bitRow r) false=bitRow r := z ▸ self_zero _
      have lt := localMono r false false false true id (by simp)
      have f := off r
      rw [self] at lt f
      have yes : target (bitRow r)=true := by cases t : target (bitRow r) <;> cases v : H (bitRow r) false <;> simp_all
      have zero : H (bitRow r) false=false := by cases v : H (bitRow r) false <;> simp_all
      have keep := truePair r ((by simpa only [self] using yes))
      have top := localMono r true false true true id (by simp) ((on_ r).trans keep)
      exact ⟨r,hr,z,yes,by intro a b; cases a <;> cases b <;> simp_all⟩
  · obtain ⟨r,hr,bad⟩ := bad true
    cases z : bitRow r 0 with
    | false => exact (bad (by simpa [z] using agrees (bitRow r))).elim
    | true =>
      have self : setZero (bitRow r) true=bitRow r := z ▸ self_zero _
      have lt := localMono r true false true true id (by simp)
      have f := on_ r
      rw [self] at lt f
      have no : target (bitRow r)=false := by cases t : target (bitRow r) <;> cases v : H (bitRow r) true <;> simp_all
      have yes : H (bitRow r) true=true := by cases v : H (bitRow r) true <;> simp_all
      have low : target (setZero (bitRow r) false)=false := by
        cases t : target (setZero (bitRow r) false)
        · rfl
        · have h := truePair r t
          simp_all
      have bot := localMono r false false false true id (by simp)
      have ofr := off r
      exact ⟨r,hr,z,no,by intro a b; cases a <;> cases b <;> simp_all⟩

end CoCofactor29
