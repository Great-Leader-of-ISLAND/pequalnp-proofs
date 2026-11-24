import PEqualNP.CoNine3024

namespace CoNine3024Budget
open CoNine3024

abbrev Counts := Fin 9 → Nat

def pack (a : Counts) : Nat :=
  a 0+32*(a 1+32*(a 2+32*(a 3+32*(a 4+32*(a 5+32*(a 6+32*(a 7+32*(a 8+32*0))))))))

theorem pack_add (a b : Counts) : pack a + pack b = pack (fun j => a j+b j) := by
  unfold pack
  omega

private theorem and_digit {x a b : Nat} (small : x≤3) (rest : a &&& b=0) :
    (x+32*a) &&& (28+32*b) = 0 := by
  have lo : ((x+32*a) &&& (28+32*b)) % 32 = 0 := by
    calc
      _ = ((x+32*a)%32) &&& ((28+32*b)%32) := Nat.and_mod_two_pow (n:=5)
      _ = x &&& 28 := by rw [show (x+32*a)%32=x by omega,show (28+32*b)%32=28 by omega]
      _ = 0 := by interval_cases x <;> decide
  have hi : ((x+32*a) &&& (28+32*b)) / 32 = 0 := by
    calc
      _ = ((x+32*a)/32) &&& ((28+32*b)/32) := Nat.and_div_two_pow (n:=5)
      _ = a &&& b := by rw [show (x+32*a)/32=a by omega,show (28+32*b)/32=b by omega]
      _ = 0 := rest
  omega

theorem pack_safe (a : Counts) (small : ∀j,a j≤3) : pack a &&& forbidden=0 := by
  rw [show forbidden=pack (fun _ => 28) by decide]
  unfold pack
  apply and_digit (small 0)
  apply and_digit (small 1)
  apply and_digit (small 2)
  apply and_digit (small 3)
  apply and_digit (small 4)
  apply and_digit (small 5)
  apply and_digit (small 6)
  apply and_digit (small 7)
  apply and_digit (small 8)
  decide

private theorem or_digit {x y a b c : Nat} (hx : x≤1) (hy : y≤1) (rest : a ||| b=c) :
    (x+32*a) ||| (y+32*b) = max x y + 32*c := by
  have lo : ((x+32*a) ||| (y+32*b)) % 32 = max x y := by
    calc
      _ = ((x+32*a)%32) ||| ((y+32*b)%32) := Nat.or_mod_two_pow (n:=5)
      _ = x ||| y := by rw [show (x+32*a)%32=x by omega,show (y+32*b)%32=y by omega]
      _ = max x y := by interval_cases x <;> interval_cases y <;> decide
  have hi : ((x+32*a) ||| (y+32*b)) / 32 = c := by
    calc
      _ = ((x+32*a)/32) ||| ((y+32*b)/32) := Nat.or_div_two_pow (n:=5)
      _ = a ||| b := by rw [show (x+32*a)/32=a by omega,show (y+32*b)/32=b by omega]
      _ = c := rest
  omega

theorem pack_or (a b : Counts) (ha : ∀j,a j≤1) (hb : ∀j,b j≤1) :
    pack a ||| pack b = pack (fun j => max (a j) (b j)) := by
  unfold pack
  apply or_digit (ha 0) (hb 0)
  apply or_digit (ha 1) (hb 1)
  apply or_digit (ha 2) (hb 2)
  apply or_digit (ha 3) (hb 3)
  apply or_digit (ha 4) (hb 4)
  apply or_digit (ha 5) (hb 5)
  apply or_digit (ha 6) (hb 6)
  apply or_digit (ha 7) (hb 7)
  apply or_digit (ha 8) (hb 8)
  decide

def flag (m : Fin 9 → Truth) (w : Truth) : Counts := fun j =>
  if (w &&& m j)=0 ∨ (w &&& m j)=m j then 1 else 0

theorem flag_le (m : Fin 9 → Truth) (w : Truth) (j : Fin 9) : flag m w j≤1 := by
  unfold flag
  split <;> decide

theorem fixedMask_pack (m : Fin 9 → Truth) (w : Truth) :
    fixedMask w (List.ofFn m)=pack (flag m w) := by rfl

def tally (d : Atom → Counts) : List Atom → Counts
  | [] => fun _ => 0
  | w::ws => fun j => d w j + tally d ws j

theorem tally_eq_count (d : Atom→Counts) (p : Atom→Fin 9→Prop) [∀ w j,Decidable (p w j)]
    (ws : List Atom) (j : Fin 9) (hw : ∀ w∈ws,d w j=if p w j then 1 else 0) :
    tally d ws j=(ws.filter (fun w => decide (p w j))).length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have ih' := ih (fun v hv => hw v (List.mem_cons_of_mem _ hv))
    simp only [tally,hw w List.mem_cons_self,List.filter_cons]
    by_cases h : p w j <;> simp [h,ih',Nat.add_comm]

theorem fold_totals (d : Atom→Counts) (ws : List Atom) (a : Counts)
    (hw : ∀w∈ws,w.fixed=pack (d w)) :
    ws.foldl (fun acc w => acc+w.fixed) (pack a)=pack (fun j => a j+tally d ws j) := by
  induction ws generalizing a with
  | nil => simp [tally]
  | cons w ws ih =>
    rw [List.foldl_cons,hw w List.mem_cons_self,pack_add,
      ih _ (fun v hv => hw v (List.mem_cons_of_mem _ hv))]
    congr 1
    funext j
    exact Nat.add_assoc ..

theorem safe_of_counts (s : State) (a : Counts) (d : Atom→Counts) (spent : s.spent=pack a)
    (fixed : ∀w∈s.wires,w.fixed=pack (d w)) (budget : ∀j,a j+tally d s.wires j≤3) :
    safe s=true := by
  unfold safe
  rw [spent,fold_totals d _ a fixed,pack_safe _ budget] <;> rfl

theorem child_spent (s : State) (a b z : Atom) (more : List Atom) (mask : Nat)
    (c x y : Counts) (hs : s.spent=pack c) (ax : a.fixed=pack x) (by' : b.fixed=pack y)
    (hx : ∀j,x j≤1) (hy : ∀j,y j≤1) :
    (child s a b z more mask).spent=pack (fun j => c j+max (x j) (y j)) := by
  change s.spent+(a.fixed ||| b.fixed)=_
  rw [hs,ax,by',pack_or x y hx hy,pack_add]

#print axioms CoNine3024Budget.safe_of_counts
#print axioms CoNine3024Budget.child_spent
end CoNine3024Budget
