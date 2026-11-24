import PEqualNP.CoPetersenDeadPath

namespace CoPetersen1669Step

open CoThetaFreeCore

abbrev Input := Fin 9 → Bool

def row (m : Nat) : Input := fun i => m.testBit i.val

def target (x : Input) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def head : TraceGate Input := ⟨.conj,primary 0,primary 3⟩

def lift (y : Fin 7 → Bool) : Input :=
  ![false, y 3, y 0, y 2, false, y 6, y 4, y 5, y 1]

theorem actual_target : restrict lift target = theta := by
  funext y
  exact (by decide +kernel : ∀ a : Fin 7 → Bool, target (lift a) = theta a) y

private theorem sources {raw : List (Input → Bool)} (i : Fin 9) (a b : Nat)
    (each : ∀ w∈raw, w=absentBit ∨ ∃ j : Fin 9, w=primary j)
    (same : ∀ j : Fin 9, j≠i → row a j = row b j) :
    agreeOutside (·=primary i) (row a) (row b) raw := by
  intro w hw hne
  rcases each w hw with rfl|⟨j,rfl⟩
  · rfl
  · apply same
    exact fun eq => hne (congrArg primary eq)

private theorem wide_ne (i : Fin 9) (a : Nat) (h : target (row a) ≠ row a i) :
    target ≠ primary i := fun e => h (congrFun e _)

private theorem primary_diff (i j : Fin 9) (a : Nat) (h : row a i ≠ row a j) :
    primary i ≠ primary j := fun e => h (congrFun e _)

theorem dichotomy (raw : List (Input → Bool)) (tail : List (TraceGate Input))
    (each : ∀ w∈raw, w=absentBit ∨ ∃ j : Fin 9, w=primary j)
    (haveP : primary (0 : Fin 9) ∈ raw) (haveQ : primary (4 : Fin 9) ∈ raw)
    (reg : registered raw (head::tail)) (solves : target∈traceWires raw (head::tail))
    (fresh : freshTrace (head.value::raw) tail) :
    (∃ j ys, j ≤ tail.length ∧ Free raw j ys ∧ target∈ys) ∨
      4 ≤ saved lift (head::tail) := by
  apply nonedge_head_dichotomy lift raw head tail (primary 0) (primary 4) target reg solves
  · exact Or.inl rfl
  · rintro (h|h)
    · exact primary_diff 0 4 1 (by decide) h
    · exact primary_diff 3 4 8 (by decide) h
  · exact wide_ne 0 1 (by decide)
  · exact wide_ne 4 16 (by decide)
  · exact ⟨row 2,row 3,sources 0 2 3 each (by decide),by decide,by decide⟩
  · intro b
    cases b
    · exact ⟨row 8,row 24,sources 4 8 24 each (by decide),by decide,by decide,by decide⟩
    · exact ⟨row 1,row 17,sources 4 1 17 each (by decide),by decide,by decide,by decide⟩
  · rfl
  · rfl
  · rfl
  · rw [actual_target]
    intro h
    have eq := congrFun h (fun _ => true)
    revert eq
    decide
  · constructor
    · intro eq
      have h := congrFun eq (row 1)
      revert h
      decide
    · intro eq
      have h := congrFun eq (row 16)
      revert h
      decide
  · intro g hg
    have h := fresh_outputs fresh g hg
    exact ⟨fun e => h (List.mem_cons_of_mem _ (e ▸ haveP)),
           fun e => h (List.mem_cons_of_mem _ (e ▸ haveQ))⟩

end CoPetersen1669Step
