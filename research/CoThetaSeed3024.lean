import PEqualNP.CoThetaSeed3024Numbers
import PEqualNP.CoAO3143SevenSemantic
import PEqualNP.CoPaid3143

namespace CoThetaSeed3024
open CoAO3143 CoAO3143Restriction CoThetaNine

def seed36 : Wire SmallInput := fun r => raw7 3 r || raw7 6 r

def bank : List (Wire SmallInput) := (List.ofFn raw7) ++ [seed36,con false,con true]

def picked (b : Bool) (i : Row) : SmallInput :=
  if b then (![5,6,9,18,24,33,66,96] : Fin 8 → SmallInput) ⟨i.val/7%8,Nat.mod_lt _ (by decide)⟩
  else (![3,42,44,52,76,81,84] : Fin 7 → SmallInput) ⟨i.val%7,Nat.mod_lt _ (by decide)⟩

def sample (w : Wire SmallInput) : Sig :=
  (SevenRoots.pack (fun i => w (picked true i)), SevenRoots.pack (fun i => w (picked false i)))

theorem sample_op (d : Bool) (a b : Wire SmallInput) : sample (op d a b) = bin d (sample a) (sample b) := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj <;> cases d <;>
    simp only [sample,op,bin,Bool.false_eq_true,↓reduceIte,BitVec.getLsbD_and,BitVec.getLsbD_or,SevenRoots.pack_bit _ _ hj]

set_option maxRecDepth 8192 in
theorem target_rows : sample ans7=target := by decide +kernel
set_option maxRecDepth 8192 in
theorem input_rows : (bank.map sample).all (fun w => w==zero || w==one || seeded.contains w)=true := by decide +kernel
set_option maxRecDepth 8192 in
theorem valid_roots : seeded.sublists.all (fun ws => unionSep false ws != top || ws==CoThetaSeed3024.plain || ws==seeded)=true := by
  decide +kernel

/-- Arbitrary straight-line AND/OR with the indicated extra OR at zero cost,
    and both Boolean constants available. Intermediate wires may be reused. -/
theorem price {n : Nat} {ws : List (Wire SmallInput)} (program : Build bank n ws)
    (hit : ans7 ∈ ws) : 11 ≤ n := by
  by_contra! small
  obtain ⟨k,S,budget,cone,roots⟩ := SevenRoots.buildCone program hit
  obtain ⟨m,T,cap,live,sub,_⟩ := cone_image cone sample target_rows sample_op
  have original (w) (hw : w∈T) : w∈seeded := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp (sub hw)
    have q := List.all_eq_true.mp input_rows (sample v) (List.mem_map_of_mem (roots v hv))
    simp only [Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at q
    rcases q with (z|o)|r
    · exact ((live_proper live _ hw).1 z).elim
    · exact ((live_proper live _ hw).2 o).elim
    · exact r
  let xs := seeded.filter fun w => decide (w∈T)
  have sl : xs.Sublist seeded := List.filter_sublist
  have equal : xs.toFinset=T := by
    ext w
    simp only [xs,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right,fun h => ⟨original w h,h⟩⟩
  have coverage : unionSep false xs=top := by simpa using live_cover live equal
  have allowed := List.all_eq_true.mp valid_roots xs (List.mem_sublists.mpr sl)
  have either : xs=CoThetaSeed3024.plain ∨ xs=seeded := by simpa [coverage] using allowed
  have run : Restricted m 0 xs.toFinset := by rw [equal]; exact unrestricted live
  rcases either with eq|eq
  · rw [eq] at run
    exact plain_impossible m (by omega) run
  · rw [eq] at run
    exact seeded_impossible m (by omega) run

end CoThetaSeed3024
