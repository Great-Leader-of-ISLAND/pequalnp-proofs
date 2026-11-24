import PEqualNP.Co4358TinyCheck

namespace CoNum4358.Tiny.Fast
open CoAO3143
set_option maxRecDepth 65536

def retain (a b : W) (ka kb : Bool) (rest : List W) : List W :=
  let r := if kb then b::rest else rest
  if ka then a::r else r

theorem retained {ws : List W} {a b : W} {U : Finset W}
    (sub : ws.toFinset=insert a (insert b U)) :
    (retain a b (decide (a∈U)) (decide (b∈U)) (remaining ws a b false false)).toFinset=U := by
  ext x
  have mem : x∈ws ↔ x=a ∨ x=b ∨ x∈U := by rw [←List.mem_toFinset,sub]; simp
  by_cases ka : a∈U <;> by_cases kb : b∈U <;>
    simp only [retain,remaining,ka,kb,decide_true,decide_false,Bool.false_eq_true,↓reduceIte,
      List.mem_toFinset,List.mem_cons,List.mem_filter,Bool.or_false,Bool.and_eq_true,bne_iff_ne,mem] <;> aesop

theorem retained_clean {ws : List W} {a b : W}
    (nd : (ws.map Prod.fst).Nodup) (ha : a∈ws) (hb : b∈ws) (ne : a≠b)
    (ka kb : Bool) : ((retain a b ka kb (remaining ws a b false false)).map Prod.fst).Nodup := by
  let r := remaining ws a b false false
  have subr : r.Sublist ws := List.filter_sublist
  have inj := List.inj_on_of_nodup_map nd
  have ab : a.1≠b.1 := fun eq => ne (inj ha hb eq)
  have nr : (r.map Prod.fst).Nodup := nd.sublist (subr.map _)
  have both (v : W) (hv : v∈ws) (side : v=a ∨ v=b) : v.1∉r.map Prod.fst := by
    intro has
    obtain ⟨x,hx,e⟩ := List.mem_map.mp has
    have eq : x=v := inj (subr.subset hx) hv e
    subst x
    change v∈remaining ws a b false false at hx
    rcases side with rfl | rfl <;> simp [remaining] at hx
  have na := both a ha (Or.inl rfl)
  have nb := both b hb (Or.inr rfl)
  change ((retain a b ka kb r).map Prod.fst).Nodup
  cases ka <;> cases kb <;> simp [retain,nr,na,nb,ab]

def possible (ws : List W) (mask : Nat) :=
  if mask==fullMask then true else
    let i := (fullMask ^^^ mask).log2
    ws.any fun w => directed w.1 (Fin.ofNat 8 (i/7)) (Fin.ofNat 7 i)

theorem possible_yes {k : Nat} {ws : List W} (h : Live k 0 ((ws.map Prod.fst).map wide).toFinset) (mask : Nat) :
    possible ws mask=true := by
  unfold possible
  split
  · rfl
  · let i := (fullMask ^^^ mask).log2
    let p := Fin.ofNat 8 (i/7)
    let n := Fin.ofNat 7 i
    have atBit (ls : List W) : (unionSep false ((ls.map Prod.fst).map wide)).getLsbD (p.val*7+n.val)=
        (ls.any fun w => directed w.1 p n) := by
      induction ls with
      | nil => simp [unionSep]
      | cons a ls ih => simp only [List.map_cons,unionSep,BitVec.getLsbD_or,joint_bit,List.any_cons,ih]
    have cov : unionSep false ((ws.map Prod.fst).map wide)=top := live_cover h rfl
    have pos : p.val*7+n.val<160 := by omega
    have eq := atBit ws
    rw [cov] at eq
    have ht : top.getLsbD (p.val*7+n.val)=true := by simp [top,BitVec.getLsbD_allOnes,pos]
    exact eq.symm.trans ht

def finish (k q : Nat) (T : Table) (ws : List W) :=
  cap ws true && cap ws false &&
    (if k==0 then ws.any isGoal else !(rectBound k (ws.map Prod.fst) || matched T q ws))

theorem finish_yes {k q T ws} (val : Valid k T) (nd : (ws.map Prod.fst).Nodup)
    (h : Trace k q ws.toFinset) : finish k q T ws=true := by
  have old := blocked_false val nd h
  unfold blocked at old
  simp only [Bool.or_eq_false_iff] at old
  have cp : (cap ws true && cap ws false)=true := by simpa using old.1.1.1
  unfold finish
  rw [cp,Bool.true_and]
  split <;> rename_i hk <;> simpa [hk] using old.2

theorem length_ok {k q : Nat} {ws : List W} (nd : (ws.map Prod.fst).Nodup)
    (h : Trace k q ws.toFinset) : ws.length≤k+1 := by
  have live := (good_of h).live
  have eq : ((ws.map Prod.fst).map wide).toFinset=ws.toFinset.image (fun w=>wide w.1) := by
    ext; simp
  rw [←eq] at live
  have n := no_over nd live
  simpa [overfull] using n

/-- A hint can only select a separating pair to test. Its arithmetic never supplies the proof. -/
def tryGate (k q : Nat) (T : Table) (ws rest : List W) (a b : W)
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
        possible fringe mask && finish k (q-payNow) T fringe))

def node (k q : Nat) (T : Table) (ws : List W) :=
  decide (ws.map Prod.fst).Nodup &&
  !(scanPairs (fun a b =>
    let rest := remaining ws a b false false
    let mask := rest.foldl (fun n w => n ||| cells w.1) 0
    options.any (tryGate k q T ws rest a b mask (cells a.1) (cells b.1))) ws)

private theorem found {k q T ws U d a b} (val : Valid k T)
    (hn : (ws.map Prod.fst).Nodup) (sub : ws.toFinset=insert a (insert b U)) (ne : a≠b)
    (bd : pay d a b≤q) (pr : (make d a b).1≠0 ∧ (make d a b).1≠32767)
    (nu : (make d a b).1∉ws.toFinset.image Prod.fst) (nr : (make d a b).1∉bare)
    (child : Trace k (q-pay d a b) (insert (make d a b) U)) (rm ca cb : Nat) :
    (options.any (tryGate k q T ws (remaining ws a b false false) a b rm ca cb))=true := by
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
  have fin := finish_yes val nd step
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
  change (decide (1+rest.length+ka.toNat+kb.toNat≤k+1) && (possible nw _ && finish k _ T nw))=true
  simp [lim,possible_yes live,fin]

theorem node_ok {k q T ws} (val : Valid k T) (yes : node k q T ws=true) : ¬Trace (k+1) q ws.toFinset := by
  intro h
  simp only [node,Bool.and_eq_true,decide_eq_true_eq] at yes
  generalize eq : ws.toFinset=S at h
  cases h with
  | step d a b ne bd pr nu nr facts child =>
    have ha : a∈ws := by rw [←List.mem_toFinset,eq]; simp
    have hb : b∈ws := by rw [←List.mem_toFinset,eq]; simp
    have nu' : (make d a b).1∉ws.toFinset.image Prod.fst := by rwa [eq]
    have A := found val yes.1 eq ne bd pr nu' nr child
    have B := found (k:=k) (q:=q) (d:=d) val yes.1 (eq.trans (Finset.insert_comm _ _ _)) ne.symm
      (by rwa [pcomm d b a]) (by rwa [mcomm d b a]) (by rwa [mcomm d b a])
      (by rwa [mcomm d b a]) (by rwa [pcomm d b a,mcomm d b a])
    have same := scanPairs_complete (fun a b =>
      let rest := remaining ws a b false false
      let mask := rest.foldl (fun n w => n ||| cells w.1) 0
      options.any (tryGate k q T ws rest a b mask (cells a.1) (cells b.1))) ha hb ne
      (A _ _ _) (B _ _ _)
    simpa [same] using yes.2

end CoNum4358.Tiny.Fast
