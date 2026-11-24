import PEqualNP.CoBitBlock4482
namespace CoSmallTail4482
open CoBitBlock4482 CoPortTrace4482

def merge (d : Bool) (a b : Mark) : Mark :=
  if d then (a.1 ||| b.1,a.2 ||| b.2) else (a.1 &&& b.1,a.2 &&& b.2)

def changed (w : Mark) := w.1 ^^^ w.2
def coverage : List Mark → Bits
  | [] => 0
  | a::xs => changed a ||| coverage xs

def picks {α : Type} : List α → List (α × List α)
  | [] => []
  | x::xs => (x,xs)::((picks xs).map fun (a,r) => (a,x::r))

/-- An unordered pair of different positions and the list after deleting both. -/
def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | x::xs => ((picks xs).map fun (y,r) => (x,y,r)) ++
    ((pairs xs).map fun (a,b,r) => (a,b,x::r))

def solve : Nat → List Mark → Bool
  | 0,ws => coverage ws == BitVec.allOnes 258
  | k+1,ws =>
    coverage ws == BitVec.allOnes 258 && (pairs ws).any fun (a,b,r) =>
      solve k (merge false a b :: r) || solve k (merge true a b :: r)

private theorem take_one {W : Type} (mark : W→Mark) (w : W) (ws : List W) (m : w∈ws) :
    ∃ rest : List W, (mark w,rest.map mark)∈picks (ws.map mark) ∧
      ∀ z∈ws, z≠w → z∈rest := by
  induction ws with
  | nil => simp at m
  | cons a ws ih =>
    rcases List.mem_cons.mp m with eq|old
    · subst w
      refine ⟨ws,by simp [picks],?_⟩
      intro z mz ne
      exact (List.mem_cons.mp mz).resolve_left ne
    · obtain ⟨r,mr,keep⟩ := ih old
      refine ⟨a::r,?_,?_⟩
      · apply List.mem_cons_of_mem
        exact List.mem_map.mpr ⟨_,mr,rfl⟩
      · intro z mz ne
        rcases List.mem_cons.mp mz with rfl|mz
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (keep z mz ne)

private theorem take_pair {W : Type} (mark : W→Mark) (a b : W) (ab : a≠b)
    (ws : List W) (ma : a∈ws) (mb : b∈ws) :
    ∃ x y r, (x=a ∧ y=b ∨ x=b ∧ y=a) ∧
      (mark x,mark y,List.map mark r) ∈ pairs (ws.map mark) ∧
      ∀ z∈ws, z≠a → z≠b → z∈r := by
  classical
  induction ws with
  | nil => simp at ma
  | cons v vs ih =>
    by_cases va : v=a
    · subst v
      have mbr := (List.mem_cons.mp mb).resolve_left (Ne.symm ab)
      obtain ⟨r,mr,keep⟩ := take_one mark b vs mbr
      refine ⟨a,b,r,Or.inl ⟨rfl,rfl⟩,?_,?_⟩
      · apply List.mem_append_left
        exact List.mem_map.mpr ⟨_,mr,rfl⟩
      · intro z mz na nb
        exact keep z ((List.mem_cons.mp mz).resolve_left na) nb
    by_cases vb : v=b
    · subst v
      have mar := (List.mem_cons.mp ma).resolve_left ab
      obtain ⟨r,mr,keep⟩ := take_one mark a vs mar
      refine ⟨b,a,r,Or.inr ⟨rfl,rfl⟩,?_,?_⟩
      · apply List.mem_append_left
        exact List.mem_map.mpr ⟨_,mr,rfl⟩
      · intro z mz na nb
        exact keep z ((List.mem_cons.mp mz).resolve_left nb) na
    obtain ⟨x,y,r,orient,mr,keep⟩ := ih
      ((List.mem_cons.mp ma).resolve_left (Ne.symm va)) ((List.mem_cons.mp mb).resolve_left (Ne.symm vb))
    refine ⟨x,y,v::r,orient,?_,?_⟩
    · apply List.mem_append_right
      exact List.mem_map.mpr ⟨_,mr,rfl⟩
    · intro z mz na nb
      rcases List.mem_cons.mp mz with rfl|mz
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (keep z mz na nb)

private theorem merge_comm (d : Bool) (a b : Mark) : merge d a b=merge d b a := by
  cases d <;> simp [merge,BitVec.and_comm,BitVec.or_comm]

private theorem read_coverage {w : Mark} {ws : List Mark} {i : Row} (mw : w∈ws)
    (diff : bit w.1 i≠bit w.2 i) : bit (coverage ws) i=true := by
  induction ws with
  | nil => simp at mw
  | cons a ws ih =>
    simp only [bit,coverage,BitVec.getLsbD_or]
    rcases List.mem_cons.mp mw with eq|m
    · subst w
      apply Bool.or_eq_true_iff.mpr
      left
      simp only [changed,BitVec.getLsbD_xor]
      change (Bool.xor (bit a.1 i) (bit a.2 i))=true
      cases x : bit a.1 i <;> cases y : bit a.2 i <;> simp_all
    · exact Bool.or_eq_true_iff.mpr (Or.inr (ih m))

private theorem all_coverage {ws : List Mark}
    (full : ∀ i : Row, ∃ w∈ws, bit w.1 i≠bit w.2 i) :
    coverage ws=BitVec.allOnes 258 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨w,m,d⟩ := full ⟨i,hi⟩
  simp only [BitVec.getLsbD_allOnes,hi,decide_true]
  exact read_coverage m d

variable {W : Type} [DecidableEq W] {join : Bool→W→W→W} {stop : Finset W→Prop}

private theorem edge_kept (mark : W→Mark)
    (hom : ∀d a b, mark (join d a b)=merge d (mark a) (mark b))
    (terminal : ∀T,stop T → ∀i : Row, ∃w∈T, bit (mark w).1 i≠bit (mark w).2 i)
    {k S} (path : Path join stop k S) (i : Row) :
    ∃w∈S,bit (mark w).1 i≠bit (mark w).2 i := by
  induction path with
  | final S h => exact terminal S h i
  | @step _ U d a b ne fresh tail ih =>
    obtain ⟨z,m,dh⟩ := ih
    rcases Finset.mem_insert.mp m with rfl|m
    · by_cases da : bit (mark a).1 i≠bit (mark a).2 i
      · exact ⟨a,Finset.mem_insert_self _ _,da⟩
      · refine ⟨b,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),?_⟩
        intro db
        apply dh
        have ea : bit (mark a).1 i=bit (mark a).2 i := by simpa using da
        rw [hom]
        cases d <;> simp only [merge,Bool.false_eq_true,↓reduceIte,bit,
          BitVec.getLsbD_and,BitVec.getLsbD_or] at ea db ⊢ <;> rw [ea,db]
    · exact ⟨z,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m),dh⟩

/-- Every genuine tight path with k gates yields a successful direct
enumeration. No branch certificates are needed; k=1 has 42 candidate
moves and k=2 at most 56 first moves followed by 42 final moves. -/
theorem physical (mark : W→Mark)
    (hom : ∀d a b, mark (join d a b)=merge d (mark a) (mark b))
    (cap : Nat) (bound : ∀T,stop T → T.card≤cap)
    (terminal : ∀T,stop T → ∀i : Row, ∃w∈T, bit (mark w).1 i≠bit (mark w).2 i)
    {k S} (path : Path join stop k S) (tight : S.card=cap+k)
    (ws : List W) (haveAll : ∀w∈S,w∈ws) : solve k (ws.map mark)=true := by
  let full : ∀ {j R}, Path join stop j R → ∀ vs : List W, (∀w∈R,w∈vs) →
      coverage (vs.map mark)=BitVec.allOnes 258 := by
    intro j R p vs hv
    apply all_coverage
    intro i
    obtain ⟨w,mw,d⟩ := edge_kept mark hom terminal p i
    exact ⟨mark w,List.mem_map.mpr ⟨w,hv w mw,rfl⟩,d⟩
  induction path generalizing ws with
  | final S h =>
    simp [solve,full (Path.final S h) ws haveAll]
  | @step k U d a b ab fresh tail ih =>
    have seen := full (Path.step d a b ab fresh tail) ws haveAll
    have hz : join d a b∉U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    have up := width bound tail
    have cn := Finset.card_insert_of_notMem hz
    have ca := Finset.card_insert_le a (insert b U)
    have cb := Finset.card_insert_le b U
    have top : (insert (join d a b) U).card=cap+k := by omega
    have na : a∉U := by
      intro m
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem m)] at tight
      omega
    have nb : b∉U := by
      intro m
      rw [Finset.insert_eq_of_mem m] at tight
      have c := Finset.card_insert_le a U
      omega
    obtain ⟨x,y,r,o,m,keep⟩ := take_pair mark a b ab ws
      (haveAll _ (Finset.mem_insert_self _ _))
      (haveAll _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
    have next := ih top (join d a b::r) (by
      intro z mz
      rcases Finset.mem_insert.mp mz with rfl|old
      · exact List.mem_cons_self
      · refine List.mem_cons_of_mem _ (keep z (haveAll z (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem old))) (fun h => na (h ▸ old)) (fun h => nb (h ▸ old))))
    have align : mark (join d a b)=merge d (mark x) (mark y) := by
      rcases o with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact hom _ _ _
      · exact (hom _ _ _).trans (merge_comm _ _ _)
    simp only [List.map_cons,align] at next
    simp only [solve,seen,beq_self_eq_true,Bool.true_and]
    apply List.any_eq_true.mpr
    refine ⟨_,m,?_⟩
    cases d
    · exact Bool.or_eq_true_iff.mpr (Or.inl next)
    · exact Bool.or_eq_true_iff.mpr (Or.inr next)

#print axioms physical
end CoSmallTail4482
