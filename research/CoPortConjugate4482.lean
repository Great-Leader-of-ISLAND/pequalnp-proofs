import PEqualNP.CoPortSymmetry4482
import PEqualNP.CoPortRoots4482

namespace CoPortRoots4482
open CoPortTrace4482 CoPortCut4482

def packRows {n : Nat} (f : Fin n → Bool) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

theorem packRows_value {n : Nat} (f : Fin n → Bool) (i : Fin n) :
    (packRows f).getLsbD i.val=f i := by
  rw [packRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
  have h : i.val < (List.ofFn f).length := by simpa only [List.length_ofFn] using i.isLt
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]
  exact List.getElem_ofFn h

def reorder (g : R ≃ R) (w : W) : W := packRows (fun r => cell w (g r))

theorem value_reorder (g : R ≃ R) (w : W) (r : R) : cell (reorder g w) r = cell w (g r) :=
  packRows_value _ r

theorem cell_ext {a b : W} (h : ∀ r : R,cell a r=cell b r) : a=b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact h ⟨i,hi⟩

theorem reorder_inj (g : R ≃ R) : Function.Injective (reorder g) := by
  intro u v eq
  apply cell_ext
  intro r
  simpa only [value_reorder,Equiv.apply_symm_apply] using congrArg (fun w => cell w (g.symm r)) eq

theorem reorder_join (g : R ≃ R) (d : Bool) (u v : W) :
    reorder g (join d u v) = join d (reorder g u) (reorder g v) := by
  apply cell_ext
  intro r
  have joinVal (a b : W) (s : R) : cell (join d a b) s =
      (if d then cell a s || cell b s else cell a s && cell b s) := model.applyJoin d a b s
  simp only [value_reorder,joinVal]

set_option maxRecDepth 4000 in
theorem reorder_path (g : R ≃ R) (inv : ∀ r, label (g r)=label r)
    {k S} (p : Path join (cleanCut model label 6) k S) :
    Path join (cleanCut model label 6) k (S.image (reorder g)) := by
  apply transport (reorder g) (reorder_inj g) (reorder_join g) _ p
  intro T terminal
  obtain ⟨cap,dist,z,o⟩ := terminal
  have h0 : reorder g (0:W)=0 := by
    apply cell_ext
    intro r
    rw [value_reorder]
    change model.val model.zero (g r)=model.val model.zero r
    rw [model.atZero,model.atZero]
  have h1 : reorder g top=top := by
    apply cell_ext
    intro r
    rw [value_reorder]
    change model.val model.one (g r)=model.val model.one r
    rw [model.atOne,model.atOne]
  refine ⟨Finset.card_image_le.trans cap,?_,?_,?_⟩
  · intro x y different
    have ne : label (g x) ≠ label (g y) := by simpa only [inv] using different
    obtain ⟨w,wt,unlike⟩ := dist (g x) (g y) ne
    refine ⟨reorder g w,Finset.mem_image_of_mem _ wt,?_⟩
    change cell (reorder g w) x ≠ cell (reorder g w) y
    rw [value_reorder,value_reorder]
    exact unlike
  · intro hit
    obtain ⟨w,hw,eq⟩ := Finset.mem_image.mp hit
    have same : w=(0 : W) := reorder_inj g (eq.trans h0.symm)
    rw [same] at hw
    exact z hw
  · intro hit
    obtain ⟨w,hw,eq⟩ := Finset.mem_image.mp hit
    have same : w=top := reorder_inj g (eq.trans h1.symm)
    rw [same] at hw
    exact o hw

end CoPortRoots4482
