import PEqualNP.CoEndpoint1888

namespace CoReaders1888
open CoRaw1888 CoEndpoint1888 CoThetaFreeCore CoThetaNine

private theorem read_saves (b : Bool) (g : TraceGate Full) (read : reads g (coord (CoEndpoint1888.ep b))) :
    disappears (lift b) g := by
  rcases read with h|h
  · exact Or.inl (h ▸ off b)
  · exact Or.inr (h ▸ off b)

theorem unique_reader (L : SignedLower) {gs : List (TraceGate Full)} (ok : sufficient roots target gs)
    (small : gs.length≤15) (b : Bool) {g t : TraceGate Full} (hg : g∈gs) (ht : t∈gs)
    (gr : reads g (coord (CoEndpoint1888.ep b))) (tr : reads t (coord (CoEndpoint1888.ep b))) : g=t := by
  classical
  by_contra ne
  have hits (v : TraceGate Full) (hq : v∈gs) (read : reads v (coord (CoEndpoint1888.ep b))) :
      v∈vanishing (lift b) gs := by simp [vanishing,hq,read_saves b v read]
  have inc : ∀v∈[g,t],v∈vanishing (lift b) gs := by
    intro v hv
    rcases List.mem_cons.mp hv with eq|hv
    · exact eq ▸ hits g hg gr
    · obtain eq := List.mem_singleton.mp hv
      exact eq ▸ hits t ht tr
  have many := length_of_cover [g,t] _ (by simp [ne]) inc
  have one := (tight_endpoints L ok small).2 b
  rw [saved_eq_length] at one
  change 2≤_ at many
  omega

/-- The sole reader must preserve every actual sensitive endpoint flip for
    which the supplied seed and the other nine inputs are held fixed. -/
theorem preserves (L : SignedLower) {gs : List (TraceGate Full)} (ok : sufficient roots target gs)
    (small : gs.length≤15) (b : Bool) {g : TraceGate Full} (hg : g∈gs)
    (gr : reads g (coord (CoEndpoint1888.ep b))) (r s : Full) (same : seed r=seed s)
    (outside : ∀i : Vertex,i≠CoEndpoint1888.ep b → r i=s i) (diff : target r≠target s) : g.value r≠g.value s := by
  have sources : agreeOutside (·=coord (CoEndpoint1888.ep b)) r s roots := by
    intro w hw skip
    rcases List.mem_cons.mp hw with rfl|hw
    · rfl
    rcases List.mem_cons.mp hw with rfl|hw
    · exact same
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact outside i (fun e => skip (congrArg coord e))
  have not_coord : target≠coord (CoEndpoint1888.ep b) := by
    intro e
    have h := congrFun e (raw 24)
    cases b <;> exact Bool.true_ne_false h
  obtain ⟨t,ht,tr,mark⟩ := reader_witness (·=coord (CoEndpoint1888.ep b)) r s ok.1 sources ok.2 not_coord diff
  exact unique_reader L ok small b ht hg tr gr ▸ mark

def pin (q : Fin 11) : Full→Bool := if h : q.val<10 then coord ⟨q.val,h⟩ else seed

def exceptions (b mode : Bool) (q : Fin 11) : Bool :=
  (q.val==(CoEndpoint1888.ep b).val) || (if mode then
    (if b then [1,4,5] else [1,3,7] : List Nat).contains q.val
    else q.val==(CoEndpoint1888.ep (!b)).val || q.val==10)

private def leftRow (b mode : Bool) : Fin 11 → Row :=
  if b then if mode then ![9,0,0,9,0,0,73,129,385,521,9] else ![0,9,0,129,9,9,9,9,9,9,0]
  else if mode then ![0,0,20,0,20,36,84,0,276,548,20] else ![0,20,0,20,36,20,20,20,20,20,0]
private def rlo (b mode : Bool) (q : Fin 11) := raw (leftRow b mode q)
private def rhi (b mode : Bool) (q : Fin 11) := raw ((leftRow b mode q)+(if b then 4 else 1))

private theorem flips : ∀ (b mode : Bool) (q : Fin 11),exceptions b mode q=false →
    let r := rlo b mode q
    let s := rhi b mode q
    seed r=seed s ∧ target r≠target s ∧ (∀i : Vertex,i≠CoEndpoint1888.ep b → r i=s i) ∧
    pin q r=mode ∧ pin q s=mode := by decide +kernel

/-- Classify every raw-or-seed companion pin of a sole endpoint reader by the
    Boolean value at which that pin masks the endpoint. The kind may be signed. -/
theorem classified (L : SignedLower) {gs : List (TraceGate Full)} (ok : sufficient roots target gs)
    (small : gs.length≤15) (b mode : Bool) {g : TraceGate Full} (hg : g∈gs)
    (gr : reads g (coord (CoEndpoint1888.ep b))) (q : Fin 11)
    (maskeq : ∀r s : Full,pin q r=mode → pin q s=mode → g.value r=g.value s) :
    exceptions b mode q=true := by
  cases test : exceptions b mode q with
  | true => rfl
  | false =>
    obtain ⟨same,diff,other,lo,hi⟩ := flips b mode q test
    exact (preserves L ok small b hg gr _ _ same other diff (maskeq _ _ lo hi)).elim

#print axioms CoReaders1888.classified
end CoReaders1888
