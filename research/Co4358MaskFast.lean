import PEqualNP.Co4358TinyFast
import PEqualNP.Co4358TinyMasks

namespace CoNum4358.Tiny.MaskFast
open CoAO3143
open Fast (retain retained retained_clean finish finish_yes length_ok)
set_option maxRecDepth 65536

abbrev Post := Nat → Nat → Table → List W → Bool
def SoundPost (post : Post) : Prop := ∀ {k q : Nat} {T : Table} {ws : List W},
  Valid k T → (ws.map Prod.fst).Nodup → Trace k q ws.toFinset → post k q T ws=true

def tryGate (post : Post) (k q : Nat) (T : Table) (ws rest : List W) (a b : W)
    (restMask ca cb : Nat) (d : Bool) :=
  let z := make d a b
  let payNow := pay d a b
  decide (payNow≤q) && z.1 != 0 && z.1 != 32767 && !(bare.contains z.1) &&
    !(ws.any fun w => w.1==z.1) &&
    (let base := restMask ||| cells z.1
     options.any fun ka => options.any fun kb =>
       decide (1+rest.length+ka.toNat+kb.toNat≤k+1) &&
       (let fringe := z::retain a b ka kb rest
        let mask := (if ka then ca else 0) ||| (if kb then cb else 0) ||| base
        Masks.complete mask && post k (q-payNow) T fringe))

def nodeWith (post : Post) (k q : Nat) (T : Table) (ws : List W) :=
  decide (ws.map Prod.fst).Nodup &&
  !(scanPairs (fun a b =>
    let rest := remaining ws a b false false
    let mask := Masks.used rest
    options.any (tryGate post k q T ws rest a b mask (cells a.1) (cells b.1))) ws)

private theorem found (post : Post) (safe : SoundPost post) {k q T ws U d a b} (val : Valid k T)
    (hn : (ws.map Prod.fst).Nodup) (sub : ws.toFinset=insert a (insert b U)) (ne : a≠b)
    (bd : pay d a b≤q) (pr : (make d a b).1≠0 ∧ (make d a b).1≠32767)
    (nu : (make d a b).1∉ws.toFinset.image Prod.fst) (nr : (make d a b).1∉bare)
    (child : Trace k (q-pay d a b) (insert (make d a b) U)) :
    (options.any (tryGate post k q T ws (remaining ws a b false false) a b
      (Masks.used (remaining ws a b false false)) (cells a.1) (cells b.1)))=true := by
  let z := make d a b
  let ka := decide (a∈U)
  let kb := decide (b∈U)
  let rest := remaining ws a b false false
  let r := retain a b ka kb rest
  let nw := z::r
  have eq : r.toFinset=U := retained sub
  have step : Trace k (q-pay d a b) nw.toFinset := by simpa [nw,eq,z] using child
  have ha : a∈ws := by rw [←List.mem_toFinset,sub]; simp
  have hb : b∈ws := by rw [←List.mem_toFinset,sub]; simp
  have ns : (r.map Prod.fst).Nodup := retained_clean hn ha hb ne ka kb
  have nu' : z.1∉r.map Prod.fst := by
    intro bad
    obtain ⟨v,hv,he⟩ := List.mem_map.mp bad
    have hu : v∈U := by rw [←eq]; exact List.mem_toFinset.mpr hv
    have hw : v∈ws.toFinset := by rw [sub]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)
    exact nu (Finset.mem_image.mpr ⟨v,hw,he⟩)
  have nd : (nw.map Prod.fst).Nodup := .cons nu' ns
  have sz : nw.length=1+rest.length+ka.toNat+kb.toNat := by
    change (z::retain a b ka kb rest).length=_
    cases ka <;> cases kb <;> simp [retain] <;> omega
  have lim : 1+rest.length+ka.toNat+kb.toNat≤k+1 := sz ▸ length_ok nd step
  have fin := safe val nd step
  have live : Live k 0 ((nw.map Prod.fst).map wide).toFinset := by
    have eq : ((nw.map Prod.fst).map wide).toFinset=nw.toFinset.image (fun w=>wide w.1) := by
      ext; simp
    rw [eq]; exact (good_of step).live
  have no : (ws.any fun w => w.1==z.1)=false := by
    apply Bool.eq_false_iff.mpr
    intro bad
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp bad
    exact nu (Finset.mem_image.mpr ⟨x,List.mem_toFinset.mpr hx,beq_iff_eq.mp he⟩)
  apply List.any_eq_true.mpr
  refine ⟨d,all_options _,?_⟩
  have en : (decide (pay d a b≤q) && z.1 != 0 && z.1 != 32767 && !(bare.contains z.1) &&
      !(ws.any fun w => w.1==z.1))=true := by
    simp [bd,show z.1∉bare from nr,no]
    exact pr
  dsimp only [tryGate]
  rw [en,Bool.true_and]
  apply List.any_eq_true.mpr
  refine ⟨ka,all_options _,List.any_eq_true.mpr ⟨kb,all_options _,?_⟩⟩
  let mask := (if ka then cells a.1 else 0) ||| (if kb then cells b.1 else 0) |||
    (Masks.used rest ||| cells z.1)
  have same : mask=Masks.used nw := by
    change ((if ka then cells a.1 else 0) ||| (if kb then cells b.1 else 0) |||
      (Masks.used rest ||| cells z.1))=Masks.used (z::retain a b ka kb rest)
    cases ka <;> cases kb <;> simp only [↓reduceIte,Bool.false_eq_true,retain,Masks.used,
      Nat.or_zero,Nat.zero_or] <;> ac_rfl
  change (decide (1+rest.length+ka.toNat+kb.toNat≤k+1) &&
    (Masks.complete mask && post k _ T nw))=true
  rw [same,Masks.needed live,fin]
  simp [lim]

theorem nodeWith_ok (post : Post) (safe : SoundPost post) {k q T ws} (val : Valid k T) (yes : nodeWith post k q T ws=true) : ¬Trace (k+1) q ws.toFinset := by
  intro h
  simp only [nodeWith,Bool.and_eq_true,decide_eq_true_eq] at yes
  generalize eq : ws.toFinset=S at h
  cases h with
  | step d a b ne bd pr nu nr facts child =>
    have ha : a∈ws := by rw [←List.mem_toFinset,eq]; simp
    have hb : b∈ws := by rw [←List.mem_toFinset,eq]; simp
    have nu' : (make d a b).1∉ws.toFinset.image Prod.fst := by rwa [eq]
    have A := found post safe val yes.1 eq ne bd pr nu' nr child
    have B := found post safe (k:=k) (q:=q) (d:=d) val yes.1 (eq.trans (Finset.insert_comm _ _ _)) ne.symm
      (by rwa [pcomm d b a]) (by rwa [mcomm d b a]) (by rwa [mcomm d b a])
      (by rwa [mcomm d b a]) (by rwa [pcomm d b a,mcomm d b a])
    have same := scanPairs_complete (fun a b =>
      let rest := remaining ws a b false false
      let mask := Masks.used rest
      options.any (tryGate post k q T ws rest a b mask (cells a.1) (cells b.1))) ha hb ne
      A B
    simpa [same] using yes.2

def node := nodeWith Fast.finish
theorem node_ok {k q T ws} (val : Valid k T) (yes : node k q T ws=true) : ¬Trace (k+1) q ws.toFinset :=
  nodeWith_ok Fast.finish (fun v n h => finish_yes v n h) val yes

end CoNum4358.Tiny.MaskFast
