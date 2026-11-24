import PEqualNP.CoBlockPartition4482

namespace CoBlockPhysical4482
open CoPortTrace4482 CoTightBlocks4482
open CoBitBlock4482 (Mark Row bit)

variable {W X : Type} [DecidableEq W]

/-- When a partition has an owner for each input wire, an actual pair of
sensitive assignment edges prevents a comparable positive/negative pair
inside any block that exclusively separates both edges. -/
theorem no_pair {ev : W → X → Bool} {S T : Finset W}
    (B : Blocks ev S T) (lo hi : Row → X) (mark : W → Mark)
    (pos : ∀ w i, bit (mark w).1 i=ev w (hi i))
    (neg : ∀ w i, bit (mark w).2 i=ev w (lo i))
    (ord : ∀ i w, w∈S → ev w (lo i)=true → ev w (hi i)=true)
    (det : ∀ i, ∃ w∈T, ev w (lo i)≠ev w (hi i))
    {t : W} (mt : t∈T) (i j : Row)
    (out : ∀ w∈S, B.owner w≠t →
      bit (mark w).1 i=bit (mark w).2 i ∧ bit (mark w).1 j=bit (mark w).2 j)
    (inside : ∀ w∈S, B.owner w=t →
      bit (mark w).1 i=true → bit (mark w).2 j=true) : False := by
  have ei : exclusive B t (lo i) (hi i) := by
    intro w mw offt
    rw [←neg w i,←pos w i]
    exact (out w mw offt).1.symm
  have ej : exclusive B t (lo j) (hi j) := by
    intro w mw offt
    rw [←neg w j,←pos w j]
    exact (out w mw offt).2.symm
  obtain ⟨w,mw,wt,p,n⟩ := block_obstruction B mt ei ej (ord i) (ord j) (det i) (det j)
  have p' : bit (mark w).1 i=true := (pos w i).trans p
  have n' : bit (mark w).2 j=false := (neg w j).trans n
  have both := inside w mw wt p'
  rw [n'] at both
  contradiction

/-- Any feasible tight physical path must pass the concrete partition test.
The input list may repeat entries or use any ordering of its live set. -/
theorem physical_possible {ev : W → X → Bool} {join : Bool → W → W → W}
    {stop : Finset W → Prop} (app : ∀ d a b x, ev (join d a b) x =
      if d then ev a x || ev b x else ev a x && ev b x)
    {cap k : Nat} {S : Finset W} (terminal : ∀ T, stop T → T.card≤cap)
    (run : Path join stop k S) (tight : S.card=cap+k)
    (lo hi : Row → X) (mark : W → Mark)
    (pos : ∀ w i, bit (mark w).1 i=ev w (hi i))
    (neg : ∀ w i, bit (mark w).2 i=ev w (lo i))
    (ord : ∀ i w, w∈S → ev w (lo i)=true → ev w (hi i)=true)
    (det : ∀ T, stop T → ∀ i, ∃ w∈T, ev w (lo i)≠ev w (hi i))
    (ws : List W) (live : ∀ w, w∈ws ↔ w∈S) :
    CoBlockPartition4482.possible
      (fun ins outs : List W =>
        !(CoBitBlock4482.invalid (ins.map mark) (outs.map mark))) cap ws []=true := by
  classical
  obtain ⟨T,st,sz,⟨B⟩⟩ := partition ev app cap terminal run tight
  apply CoBlockPartition4482.possible_of_owner _ B.owner S cap T sz ws []
  · intro w m
    exact B.lands w ((live w).mp m)
  · simp
  · intro t mt
    obtain ⟨w,m,e⟩ := B.onto t mt
    exact ⟨w,(live w).mpr m,e⟩
  · exact fun w m => Or.inl ((live w).mpr m)
  · intro t mt ins outside inward outward covered
    change !(CoBitBlock4482.invalid (ins.map mark) (outside.map mark))=true
    cases h : CoBitBlock4482.invalid (ins.map mark) (outside.map mark) with
    | false => rfl
    | true =>
      obtain ⟨i,j,out,inside⟩ := CoBitBlock4482.invalid_witness _ _ h
      exfalso
      apply no_pair B lo hi mark pos neg ord (det T st) mt i j
      · intro w m ne
        rcases covered w m with inside'|outside'
        · exact (ne (inward w inside')).elim
        · exact out _ (List.mem_map.mpr ⟨w,outside',rfl⟩)
      · intro w m e
        rcases covered w m with inside'|outside'
        · exact inside _ (List.mem_map.mpr ⟨w,inside',rfl⟩)
        · exact (outward w outside' e).elim

#print axioms physical_possible
end CoBlockPhysical4482
