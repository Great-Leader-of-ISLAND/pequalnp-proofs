import PEqualNP.Co4358TinyMasks
namespace CoNum4358.Tiny.Corners
open CoAO3143
set_option maxRecDepth 65536

def counts : List K → Nat × Nat
  | [] => (0,0)
  | a::xs => let r := counts xs; let w := cells a; (w ||| r.1,r.2 ||| (w &&& r.1))

theorem seen {xs : List K} {a : K} (ha : a∈xs) (i : Nat) (yes : (cells a).testBit i=true) :
    (counts xs).1.testBit i=true := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.mem_cons] at ha
    rcases ha with rfl | ha
    · simp [counts,Nat.testBit_or,yes]
    · simp [counts,Nat.testBit_or,ih ha]

theorem repeated {xs : List K} {a b : K} (ha : a∈xs) (hb : b∈xs) (ne : a≠b)
    (i : Nat) (pa : (cells a).testBit i=true) (pb : (cells b).testBit i=true) :
    (counts xs).2.testBit i=true := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact False.elim (ne rfl)
      · simp [counts,Nat.testBit_or,Nat.testBit_and,pa,seen hb i pb]
    · rcases hb with rfl | hb
      · simp [counts,Nat.testBit_or,Nat.testBit_and,pb,seen ha i pa]
      · simp [counts,Nat.testBit_or,ih ha hb]

def exclusive (xs : List K) := (counts xs).1 ^^^ (counts xs).2

theorem owns {xs : List K} {a : K} (ha : a∈xs) (p : Fin 8) (n : Fin 7)
    (hit : (cells a &&& exclusive xs).testBit (p.val*7+n.val)=true) :
    forced xs p n a=true := by
  let i := p.val*7+n.val
  change (cells a &&& exclusive xs).testBit i=true at hit
  rw [Nat.testBit_and,Bool.and_eq_true] at hit
  have one := seen ha i hit.1
  have no : (counts xs).2.testBit i=false := by
    have eq := hit.2
    rw [exclusive,Nat.testBit_xor,one] at eq
    cases h : (counts xs).2.testBit i <;> simp_all
  apply List.all_eq_true.mpr
  intro b hb
  by_cases eq : b=a
  · simp [eq]
  · have noB : directed b p n=false := by
      apply Bool.eq_false_iff.mpr
      intro dy
      have dy' : (cells b).testBit i=true := by simpa [i,Masks.cells_bit] using dy
      exact Bool.false_ne_true (no.symm.trans (repeated ha hb (Ne.symm eq) i hit.1 dy'))
    change (b==a || !(b.getLsbD p.val) || b.getLsbD (8+n.val))=true
    cases x : b.getLsbD p.val <;> cases y : b.getLsbD (8+n.val) <;> simp_all [directed]

def tagged (xs : List K) (a : K) := prof a (exclusive xs)

def pair (x y : Prof) :=
  match propose x y with
  | none => false
  | some r => x.wire != y.wire &&
    x.unique.testBit (r.p.val*7+r.m₁.val) && x.unique.testBit (r.q₁.val*7+r.n.val) &&
    y.unique.testBit (r.p.val*7+r.m₂.val) && y.unique.testBit (r.q₂.val*7+r.n.val)

theorem pair_no {k xs} (h : Live k 0 (xs.map wide).toFinset)
    (tight : (xs.map wide).toFinset.card=k+1) {a b} (ha : a∈xs) (hb : b∈xs) :
    pair (tagged xs a) (tagged xs b)=false := by
  apply Bool.eq_false_iff.mpr
  intro yes
  unfold pair at yes
  split at yes
  · contradiction
  · rename_i r hr
    simp only [Bool.and_eq_true] at yes
    let witness : Rect := ⟨a,b,r.p,r.q₁,r.q₂,r.n,r.m₁,r.m₂⟩
    have bad : validRect xs witness=true := by
      change ((a != b) && forced xs r.p r.m₁ a && forced xs r.q₁ r.n a &&
        forced xs r.p r.m₂ b && forced xs r.q₂ r.n b)=true
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨⟨yes.1.1.1.1,owns ha _ _ yes.1.1.1.2⟩,owns ha _ _ yes.1.1.2⟩,
        owns hb _ _ yes.1.2⟩,owns hb _ _ yes.2⟩
    exact Bool.false_ne_true ((invalid h tight witness).symm.trans bad)

def clash (xs : List K) :=
  let r := counts xs
  let only := r.1 ^^^ r.2
  scanPairs pair (xs.map fun a => prof a only)

private theorem scan_nil {α} (f : α → α → Bool) (as : List α)
    (zero : ∀a∈as,∀b∈as,f a b=false) : scanPairs f as=false := by
  induction as with
  | nil => rfl
  | cons a xs ih =>
    have na : (xs.any (f a))=false := by
      apply Bool.eq_false_iff.mpr
      intro hit
      obtain ⟨b,hb,yes⟩ := List.any_eq_true.mp hit
      exact Bool.false_ne_true ((zero a (List.mem_cons_self) b (List.mem_cons_of_mem _ hb)).symm.trans yes)
    have rest : scanPairs f xs=false := ih (fun a ha b hb =>
      zero a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
    simp only [scanPairs,na,rest,Bool.false_or]

theorem clash_no {k xs} (h : Live k 0 (xs.map wide).toFinset)
    (tight : (xs.map wide).toFinset.card=k+1) : clash xs=false := by
  change scanPairs pair (xs.map (tagged xs))=false
  apply scan_nil
  intro a ha b hb
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ha
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hb
  exact pair_no h tight hu hv

end CoNum4358.Tiny.Corners
