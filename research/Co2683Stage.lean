import PEqualNP.CoSignedBudget
namespace PEqualNP.Research.SignStage
open PEqualNP.Outside.L_meta_1667
open SignedBudget
def pairs : List (Sig × Row × Row) := List.ofFn (fun i : Fin 9 =>
  (inputs.getD i.val zero,absentRow i,presentRow i))
theorem base_lower : Lower inputs graph 15 := by
  apply lower_impossible graph_proper _ (dead_start (before_sound known383 valid383) geomdead tablesdead)
  have cert : checkEssential graph inputs pairs = true := by decide +kernel
  have same : pairs.map Prod.fst = inputs := by decide +kernel
  intro a ha
  apply essential_ok cert a
  exact List.mem_toFinset.mpr (same.symm ▸ ha)

theorem priced (m : Nat) (op : Fin m → Bool) (a b : Fin m → Nat × Bool) (out : Nat × Bool)
    (S : Finset Nat) (v : (Fin 9 → Bool) → Nat → Bool)
    (before : ∀ i, (a i).1 < 10+i.val ∧ (b i).1 < 10+i.val)
    (output : out.1 < 10+m)
    (perm : let ok := fun t : Nat × Bool => t.2=true → t.1=0 ∨ t.1=9 ∨ t.1∈S
            ok out ∧ ∀ i, ok (a i) ∧ ok (b i))
    (vars : ∀ x (i : Fin 9), v x i.val = x i)
    (z : ∀ x, v x 9=false)
    (step : ∀ x i, (v x (10+i.val)) =
       if op i then ((v x (a i).1 ^^ (a i).2) && (v x (b i).1 ^^ (b i).2))
       else ((v x (a i).1 ^^ (a i).2) || (v x (b i).1 ^^ (b i).2)))
    (computed : ∀ x, (v x out.1 ^^ out.2) = edge x) :
    15 ≤ m + (insert 0 S).card := by
  classical
  let K := insert 0 S
  let w : Nat → Wire Row := fun j r => v (sample r) j
  have nine : Constant (w 9) := ⟨false,funext (fun r => z (sample r))⟩
  have raw (i : Nat) (hi : i < 10) : Available (inputs.map observe) (w i) := by
    by_cases h : i < 9
    · let t : Fin 9 := ⟨i,h⟩
      have eq : w i = observe (inputs.getD i zero) := funext (fun r => vars (sample r) t)
      rw [eq]
      have elm : inputs.getD i zero ∈ List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) :=
        List.mem_ofFn.mpr ⟨t,rfl⟩
      rw [input_list] at elm
      exact Or.inl (List.mem_map_of_mem elm)
    · obtain rfl : i=9 := by omega
      exact Or.inr nine
  have paid (t : Nat × Bool) (h : t.2=true → t.1=0 ∨ t.1=9 ∨ t.1∈S) :
      t.2=true → t.1∈K ∨ Constant (w t.1) := by
    intro ht
    rcases h ht with e | e | e
    · exact Or.inl (Finset.mem_insert.mpr (Or.inl e))
    · rw [e]; exact Or.inr nine
    · exact Or.inl (Finset.mem_insert_of_mem e)
  have read (t : Nat × Bool) (r : Row) :
      lit w t r = (v (sample r) t.1 ^^ t.2) := by
    rcases t with ⟨j,s⟩
    cases s <;> simp [lit,inv,w]
  have logic (j : Nat) (lo : 10 ≤ j) (hi : j < 10+m) : ∃ (isOr : Bool) (c d : Nat × Bool),
      c.1 < j ∧ d.1 < j ∧ (c.2=true → c.1∈K ∨ Constant (w c.1)) ∧
      (d.2=true → d.1∈K ∨ Constant (w d.1)) ∧ w j = combine isOr (lit w c) (lit w d) := by
    let i : Fin m := ⟨j-10,by omega⟩
    have hj : 10+i.val=j := by dsimp [i]; omega
    refine ⟨!(op i),a i,b i,hj ▸ (before i).1,hj ▸ (before i).2,
      paid _ (perm.2 i).1,paid _ (perm.2 i).2,?_⟩
    funext r
    have eq := step (sample r) i
    rw [hj] at eq
    cases h : op i <;> simpa [combine,h,read,w] using eq
  obtain ⟨p,bank,reach,known,_,hp⟩ := budget w K _ 10 m raw logic (10+m) (le_refl _)
  have hit := signed_avail known out output (paid _ perm.1)
  have target : lit w out = observe graph := by
    funext r
    exact (read out r).trans ((computed _).trans (edge_table r).symm)
  rw [target] at hit
  have lower := base_lower p bank reach hit
  have bound : (pref K (10+m)).card ≤ K.card := Finset.card_le_card (Finset.filter_subset _ _)
  change 15 ≤ m + K.card
  omega
end PEqualNP.Research.SignStage
