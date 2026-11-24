import PEqualNP.CoPortMoves4482
namespace CoTightBlocks4482
open CoPortTrace4482
variable {W X : Type} [DecidableEq W]

structure Blocks (ev : W → X → Bool) (S T : Finset W) where
  owner : W → W
  lands : ∀ w∈S, owner w∈T
  onto : ∀ t∈T, ∃ w∈S, owner w=t
  mono : ∀ t∈T, ∀ p n : X,
    (∀ w∈S, owner w=t → ev w p=true → ev w n=true) → ev t p=true → ev t n=true

/-- If the remaining number of gates is exactly the necessary drop in live
wire count, every gate consumes its two operands at their final uses. -/
theorem partition {join : Bool → W → W → W} {stop : Finset W → Prop}
    (ev : W → X → Bool) (app : ∀ d a b x, ev (join d a b) x =
      if d then ev a x || ev b x else ev a x && ev b x)
    (cap : Nat) (terminal : ∀ T, stop T → T.card≤cap)
    {k S} (run : Path join stop k S) (tight : S.card=cap+k) :
    ∃ T, stop T ∧ T.card=cap ∧ Nonempty (Blocks ev S T) := by
  induction run with
  | final S h =>
    refine ⟨S,h,by simpa using tight,⟨⟨id,fun _ m => m,fun t m => ⟨t,m,rfl⟩,?_⟩⟩⟩
    intro t ht p n h yes
    exact h t ht rfl yes
  | @step k U d a b ab fresh tail ih =>
    let z := join d a b
    have hz : z∉U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    have up := width terminal tail
    change (insert z U).card≤cap+k at up
    have zsize := Finset.card_insert_of_notMem hz
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    have tailSize : (insert z U).card=cap+k := by omega
    have absentA : a∉insert b U := by
      intro m
      rw [Finset.insert_eq_of_mem m] at tight
      omega
    have absentB : b∉U := by
      intro m
      rw [Finset.insert_eq_of_mem m] at tight
      have q := Finset.card_insert_le a U
      omega
    obtain ⟨T,st,sz,⟨B⟩⟩ := ih tailSize
    let owner := fun w : W => if w=a ∨ w=b then B.owner z else B.owner w
    have old {w : W} (m : w∈U) : owner w=B.owner w := by
      have na : w≠a := by rintro rfl; exact absentA (Finset.mem_insert_of_mem m)
      have nb : w≠b := by rintro rfl; exact absentB m
      simp [owner,na,nb]
    have oa : owner a=B.owner z := by simp [owner]
    have ob : owner b=B.owner z := by simp [owner]
    have ma : a∈insert a (insert b U) := Finset.mem_insert_self _ _
    have mb : b∈insert a (insert b U) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have inc {w : W} (m : w∈U) : w∈insert a (insert b U) :=
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m)
    refine ⟨T,st,sz,⟨⟨owner,?_,?_,?_⟩⟩⟩
    · intro w mw
      rcases Finset.mem_insert.mp mw with rfl|mw
      · rw [oa]; exact B.lands _ (Finset.mem_insert_self _ _)
      rcases Finset.mem_insert.mp mw with rfl|mw
      · rw [ob]; exact B.lands _ (Finset.mem_insert_self _ _)
      rw [old mw]
      exact B.lands _ (Finset.mem_insert_of_mem mw)
    · intro t ht
      obtain ⟨w,m,e⟩ := B.onto t ht
      rcases Finset.mem_insert.mp m with rfl|mw
      · exact ⟨a,ma,oa.trans e⟩
      · exact ⟨w,inc mw,(old mw).trans e⟩
    · intro t ht p n order
      apply B.mono t ht p n
      intro w m e
      rcases Finset.mem_insert.mp m with rfl|mw
      · have ao := order a ma (oa.trans e)
        have bo := order b mb (ob.trans e)
        change ev (join d a b) p=true → ev (join d a b) n=true
        rw [app,app]
        cases d <;> simp only [↓reduceIte,Bool.false_eq_true,Bool.and_eq_true,Bool.or_eq_true]
        · exact fun h => ⟨ao h.1,bo h.2⟩
        · exact fun h => h.imp ao bo
      · exact order w (inc mw) ((old mw).trans e)

def exclusive {ev : W → X → Bool} {S T} (B : Blocks ev S T) (t : W) (lo hi : X) :=
  ∀ w∈S, B.owner w≠t → ev w lo=ev w hi

theorem priceEdge {ev : W → X → Bool} {S T} (B : Blocks ev S T) {t : W} {lo hi : X}
    (exclusiveTo : exclusive B t lo hi) (ordered : ∀ w∈S, ev w lo=true → ev w hi=true)
    (dist : ∃ z∈T, ev z lo≠ev z hi) : ev t lo=false ∧ ev t hi=true := by
  obtain ⟨z,m,diff⟩ := dist
  have zt : z=t := by
    by_contra n
    have back := B.mono z m hi lo (by
      intro w h owner up
      have no : B.owner w≠t := fun e => n (owner.symm.trans e)
      rw [exclusiveTo w h no]
      exact up)
    have front := B.mono z m lo hi (fun w h _ => ordered w h)
    cases a : ev z lo <;> cases b : ev z hi <;> simp_all
  subst t
  have f := B.mono z m lo hi (fun w h _ => ordered w h)
  cases a : ev z lo <;> cases b : ev z hi <;> simp_all

/-- Two sensitive edges whose separators all belong to the same leaf block
force the block's one output to be true on each positive endpoint and false
on each negative endpoint. Cross-comparison prevents a monotone realization. -/
theorem block_obstruction {ev : W → X → Bool} {S T} (B : Blocks ev S T) {t : W} (ht : t∈T)
    {lo hi lo' hi' : X} (one : exclusive B t lo hi) (two : exclusive B t lo' hi')
    (or1 : ∀ w∈S, ev w lo=true → ev w hi=true) (or2 : ∀ w∈S, ev w lo'=true → ev w hi'=true)
    (d1 : ∃ z∈T, ev z lo≠ev z hi) (d2 : ∃ z∈T, ev z lo'≠ev z hi') :
    ∃ w∈S, B.owner w=t ∧ ev w hi=true ∧ ev w lo'=false := by
  have p := (priceEdge B one or1 d1).2
  have n := (priceEdge B two or2 d2).1
  by_contra absent
  have pos := B.mono t ht hi lo' (by
    intro w m o yes
    cases e : ev w lo' with
    | false => exact (absent ⟨w,m,o,yes,e⟩).elim
    | true => rfl) p
  rw [n] at pos
  contradiction

#print axioms partition
#print axioms block_obstruction
end CoTightBlocks4482
