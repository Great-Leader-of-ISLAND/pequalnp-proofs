import PEqualNP.Co4358TinyModel
namespace CoNum4358.Tiny.Reflection
open CoAO3143
set_option maxRecDepth 65536

def order : Fin 15 → Fin 15 := ![7,4,5,6,1,2,3,0,8,14,11,10,12,13,9]
def reverseK (w : K) : K :=
  (BitVec.ofBoolListLE (List.ofFn (fun i : Fin 15 => w.getLsbD (order i).val))).cast List.length_ofFn

theorem reverse_bit (w : K) (i : Fin 15) : (reverseK w).getLsbD i.val=w.getLsbD (order i).val := by
  rw [reverseK,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
  have bd : i.val<(List.ofFn (fun j : Fin 15 => w.getLsbD (order j).val)).length := by simpa using i.isLt
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem bd]
  exact List.getElem_ofFn bd

theorem invol (w : K) : reverseK (reverseK w)=w := by
  have inv : ∀i : Fin 15,order (order i)=i := by decide +kernel
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin 15 := ⟨j,hj⟩
  change (reverseK (reverseK w)).getLsbD i.val=w.getLsbD i.val
  rw [reverse_bit,reverse_bit,inv]

theorem injK : Function.Injective reverseK := Function.LeftInverse.injective invol

theorem op (d : Bool) (a b : K) : reverseK (makeKW d a b)=makeKW d (reverseK a) (reverseK b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin 15 := ⟨j,hj⟩
  change (reverseK (makeKW d a b)).getLsbD i.val=(makeKW d (reverseK a) (reverseK b)).getLsbD i.val
  cases d <;> simp only [reverse_bit,makeKW,Bool.false_eq_true,↓reduceIte,BitVec.getLsbD_and,BitVec.getLsbD_or]

theorem constants : reverseK 0=0 ∧ reverseK 32767=32767 ∧ reverseK 255=255 ∧ reverseK 7442=7442 := by
  decide +kernel

theorem raw_fixed : (bare.map reverseK).toFinset=bare.toFinset := by decide +kernel

def wire (w : W) : W := (reverseK w.1,(w.2.2,w.2.1))
theorem wire_invol (w : W) : wire (wire w)=w := by
  rcases w with ⟨s,a,b⟩
  change (reverseK (reverseK s),(a,b))=(s,(a,b))
  rw [invol]
theorem wire_inj : Function.Injective wire := Function.LeftInverse.injective wire_invol

theorem combine (d : Bool) (a b : W) : wire (make d a b)=make d (wire a) (wire b) :=
  Prod.ext (op d a.1 b.1) rfl

private theorem read_fee (w : K) : (reverseK w==7442)=(w==7442) := by
  by_cases eq : w=7442
  · simp [eq,constants.2.2.2]
  · have m : reverseK w≠7442 := fun z => eq (injK (z.trans constants.2.2.2.symm))
    simp [eq,m]
theorem price (d : Bool) (u v : W) : pay d (wire u) (wire v)=pay d u v := by
  simp only [pay,wire,read_fee]

def Represented (a : Sig) := ∃t : K,wide t=a
noncomputable def renameSig (a : Sig) := wide (reverseK (Function.invFun wide a))

theorem rename_wide (a : K) : renameSig (wide a)=wide (reverseK a) := by
  rw [renameSig,Function.leftInverse_invFun wide_inj a]

private theorem faithful {a b : Sig} (ma : Represented a) (mb : Represented b)
    (eq : renameSig a=renameSig b) : a=b := by
  obtain ⟨x,rfl⟩ := ma
  obtain ⟨y,rfl⟩ := mb
  rw [rename_wide,rename_wide] at eq
  exact congrArg wide (injK (wide_inj eq))

private theorem preserves_proper {a : Sig} (ma : Represented a) (h : proper a) : proper (renameSig a) := by
  have ez : renameSig zero=zero := by rw [←zero_value,rename_wide,constants.1]
  have eo : renameSig one=one := by rw [←one_value,rename_wide,constants.2.1]
  exact ⟨fun eq => h.1 (faithful ma ⟨0,zero_value⟩ (eq.trans ez.symm)),
    fun eq => h.2 (faithful ma ⟨32767,one_value⟩ (eq.trans eo.symm))⟩

private theorem preserves_bin (d : Bool) {a b : Sig} (ma : Represented a) (mb : Represented b) :
    Represented (bin d a b) ∧ renameSig (bin d a b)=bin d (renameSig a) (renameSig b) := by
  obtain ⟨x,rfl⟩ := ma
  obtain ⟨y,rfl⟩ := mb
  exact ⟨⟨makeKW d x y,wide_bin d x y⟩,by rw [←wide_bin,rename_wide,rename_wide,rename_wide,op,wide_bin]⟩

theorem mirror_live {k t S} (h : Live k t S) (hz : t=0) (all : ∀v∈S,Represented v) :
    Live k 0 (S.image renameSig) := by
  induction h with
  | stop =>
    have fixed : renameSig target=target := by rw [←target_value,rename_wide,constants.2.2.1]
    simpa [fixed] using (Live.stop : Live 0 0 {target})
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb ne fresh tail ih =>
    have ma : Represented a := all _ (by simp)
    have mb : Represented b := all _ (by simp)
    have bz := preserves_bin d ma mb
    have mu (u : Sig) (hu : u∈U) : Represented u := all u (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))
    have child := ih hz (fun u hu => by
      obtain eq|old := Finset.mem_insert.mp hu
      · rw [eq]; exact bz.1
      · exact mu u old)
    simp only [Finset.image_insert,bz.2] at child ⊢
    apply Live.binary (preserves_proper ma ha) (preserves_proper mb hb)
      (fun e => ne (faithful ma mb e)) _ child
    intro bad
    rw [←bz.2,←Finset.image_insert,←Finset.image_insert] at bad
    obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp bad
    exact fresh (by simpa only [faithful (all _ hv) bz.1 eq] using hv)

theorem good {k : Nat} {S : Finset W} (h : Good k S) : Good k (S.image wire) := by
  constructor
  · have live := mirror_live h.live rfl (fun v hv => by
      obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hv
      exact ⟨w.1,rfl⟩)
    have sets : (S.image (fun w => wide w.1)).image renameSig=(S.image wire).image (fun w=>wide w.1) := by
      simp only [Finset.image_image,Function.comp_def,wire,rename_wide]
    rwa [←sets]
  · intro s
    obtain ⟨w,hw,hits⟩ := h.caps (!s)
    exact ⟨wire w,Finset.mem_image_of_mem _ hw,by cases s <;> exact hits⟩

theorem trace {k q S} (h : Trace k q S) : Trace k q (S.image wire) := by
  induction h with
  | done q w a b c =>
    simp only [Finset.image_singleton]
    exact Trace.done q (wire w) (by change reverseK w.1=255; rw [a,constants.2.2.1]) c b
  | @step k q U d a b ne budget clean unused raw facts child ih =>
    have ori : ∀t : K,reverseK t∈bare → t∈bare := by
      intro t ht
      have m : reverseK (reverseK t)∈(bare.map reverseK).toFinset := by
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨reverseK t,ht,rfl⟩)
      simpa only [invol,raw_fixed,List.mem_toFinset] using m
    have eq : (make d (wire a) (wire b)).1=reverseK (make d a b).1 :=
      congrArg Prod.fst (combine d a b).symm
    have source := good facts
    simp only [Finset.image_insert] at source ⊢
    simp only [Finset.image_insert,combine] at ih
    apply Trace.step d (wire a) (wire b) (fun h => ne (wire_inj h)) (by rwa [price]) _ _ _
      source (by simpa only [price] using ih)
    · rw [eq]
      exact ⟨fun e=>clean.1 (injK (e.trans constants.1.symm)),
        fun e=>clean.2 (injK (e.trans constants.2.1.symm))⟩
    · intro bad
      rw [eq,←Finset.image_insert,←Finset.image_insert] at bad
      obtain ⟨w,hw,ev⟩ := Finset.mem_image.mp bad
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      exact unused (Finset.mem_image.mpr ⟨v,hv,injK ev⟩)
    · rw [eq]
      exact fun e=>raw (ori _ e)

#print axioms trace
end CoNum4358.Tiny.Reflection
