import PEqualNP.CoPortSymmetry4482
import PEqualNP.CoPortRoots4482

namespace CoPortRoots4482
open CoPortTrace4482 CoPortCut4482

def reorder (g : R ≃ R) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun r : R => cell w (g r)))).cast List.length_ofFn

theorem value_reorder (g : R ≃ R) (w : W) (r : R) : cell (reorder g w) r = cell w (g r) := by
  simp only [cell,reorder,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD,List.getElem?_ofFn,r.isLt,↓reduceDIte,Option.getD_some]

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
    exact ⟨reorder g w,Finset.mem_image_of_mem _ wt,by simpa only [value_reorder] using unlike⟩
  · intro hit
    obtain ⟨w,hw,eq⟩ := Finset.mem_image.mp hit
    exact z ((reorder_inj g (eq.trans h0.symm)) ▸ hw)
  · intro hit
    obtain ⟨w,hw,eq⟩ := Finset.mem_image.mp hit
    exact o ((reorder_inj g (eq.trans h1.symm)) ▸ hw)

end CoPortRoots4482
