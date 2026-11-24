import PEqualNP.CoBudget3825Base

namespace PEqualNP.Outside.L_meta_2153_aux.CoDelete4139
open CoThetaFreeCore CoThetaNine
abbrev Ten := Fin 10 → Bool

def x (i : Fin 10) (r : Ten) := r i
def port (r : Ten) := r 0 || r 1
def raw : List (Ten → Bool) := absentBit :: port :: List.ofFn x
def petersen (r : Ten) : Bool :=
  (r 0 && r 1) || (r 1 && r 2) || (r 2 && r 3) || (r 3 && r 4) || (r 4 && r 0) ||
  (r 0 && r 5) || (r 1 && r 6) || (r 2 && r 7) || (r 3 && r 8) || (r 4 && r 9) ||
  (r 5 && r 7) || (r 7 && r 9) || (r 9 && r 6) || (r 6 && r 8) || (r 8 && r 5)

def names : Fin 10 → Option (Fin 9) :=
  ![none, some 4, some 0, some 1, some 6, some 7, some 3, some 5, some 2, some 8]
def liftRow (r : Input) (i : Fin 10) : Bool := (names i).elim false (fun j => vtx j r)

def single : Ten := fun i => decide (i = 1)
def pair : Ten := fun i => decide (i = 0 ∨ i = 1)

theorem agrees : agreeOutside (· = x 0) single pair raw := by
  intro f hf ne
  rcases List.mem_cons.mp hf with rfl|hf
  · rfl
  rcases List.mem_cons.mp hf with rfl|hf
  · decide
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
  have hi : i ≠ 0 := by intro eq; exact ne (eq ▸ rfl)
  simp [single,pair,x,hi]

theorem projected : ∀ f ∈ raw, restrict liftRow f ∈ vertices := by
  intro f hf
  rcases List.mem_cons.mp hf with rfl|hf
  · exact List.mem_cons_self
  rcases List.mem_cons.mp hf with rfl|hf
  · have e : restrict liftRow port = vtx 4 := by funext r; rfl
    rw [e]
    exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨4,rfl⟩)
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
  cases eq : names i with
  | none =>
    have e : restrict liftRow (x i) = absentBit := by
      funext r
      simp [x,restrict,liftRow,eq,absentBit]
    exact e ▸ List.mem_cons_self
  | some j =>
    have e : restrict liftRow (x i) = vtx j := by
      funext r
      simp [x,restrict,liftRow,eq]
    rw [e]
    exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨j,rfl⟩)

set_option maxHeartbeats 3000000 in
theorem slice : ∀ r : Input, petersen (liftRow r) = ans r := by decide +kernel

theorem fifteen (cert : SignedLower) (gs : List (TraceGate Ten))
    (ok : sufficient raw petersen gs) : 15 ≤ gs.length := by
  classical
  have ni : petersen ≠ x 0 := by
    intro h
    exact (by decide : petersen (fun i => decide (i = 0)) ≠ x 0 (fun i => decide (i = 0)))
      (congrFun h _)
  obtain ⟨g,hg,read,_⟩ := reader_witness (· = x 0) single pair ok.1 agrees ok.2 ni
    (by decide : petersen single ≠ petersen pair)
  have zero : restrict liftRow (x 0) = absentBit := by funext r; rfl
  have dead := reading_zero_disappears liftRow zero (show reads g (x 0) from read)
  have mem : g ∈ vanishing liftRow gs := by simp [vanishing,hg,dead]
  have one : 1 ≤ saved liftRow gs := by
    rw [saved_eq_length]
    exact length_of_cover [g] _ (by simp) (by simpa using mem)
  obtain ⟨ws,run,use⟩ := restrict_trace liftRow gs ok.1
    (Free.start (raw:=vertices)) List.mem_cons_self projected
  obtain ⟨ts,ln,reg,last⟩ := trace_of_free run
  have hit := use petersen ok.2
  rw [show restrict liftRow petersen = ans from funext slice] at hit
  have bound := any_nine_lower cert (gs:=ts) ⟨reg,last ▸ hit⟩
  have account := accounted liftRow gs
  omega

#print axioms fifteen
end PEqualNP.Outside.L_meta_2153_aux.CoDelete4139
