import PEqualNP.Co4358Shadow

namespace CoNum4358.RectCheck
open CoAO3143

structure Table where
  count : Nat
  row : Nat → Nat × List AugWire
  place : Nat → List AugWire → Nat

def Valid (k : Nat) (T : Table) : Prop :=
  ∀ i<T.count, ¬ Shadow k (T.row i).1 (T.row i).2.toFinset

def matched (T : Table) (q : Nat) (ws : List AugWire) : Bool :=
  let i := T.place q ws
  decide (i<T.count) && ((T.row i).1 == q) && ws.isPerm (T.row i).2

theorem matched_false {T k q ws} (v : Valid k T) (s : Shadow k q ws.toFinset) :
    matched T q ws=false := by
  apply Bool.eq_false_iff.mpr
  intro bad
  simp only [matched,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,List.isPerm_iff] at bad
  obtain ⟨⟨idx,qeq⟩,perm⟩ := bad
  have eqs : ws.toFinset=(T.row (T.place q ws)).2.toFinset := by
    ext t
    simpa using perm.mem_iff (a:=t)
  exact v _ idx (by rwa [qeq,←eqs])

theorem local_of {k q S} (run : Shadow k q S) : Local k S := by
  cases run with
  | done q w orig ok1 ok2 =>
    constructor
    · simpa [orig] using Live.stop
    · intro side
      exact ⟨w,Finset.mem_singleton_self _,by cases side <;> assumption⟩
  | step _ _ _ _ _ _ _ _ h _ => exact h

def cover (ws : List AugWire) (s : Bool) := ws.any fun w => capability s w.2
def baseWire (w : AugWire) := w.1==target && w.2.1.separates && w.2.2.separates

private theorem zero_member {q S} (h : Shadow 0 q S) : ∃ u∈S, baseWire u=true := by
  cases h with
  | done q w orig h₀ h₃ => exact ⟨w,Finset.mem_singleton_self _,by simp [baseWire,orig,h₀,h₃]⟩

def rectCheck (ws : List Sig) : Bool :=
  (Memo.wordHint thisGrid ws).any (ProtocolProof.verify ws)

theorem rectCheck_false {k ws} (h : Live k 0 ws.toFinset) (tight : ws.toFinset.card=k+1) :
    rectCheck ws=false := by
  unfold rectCheck
  cases eq : Memo.wordHint thisGrid ws with
  | none => rfl
  | some cert => exact ProtocolProof.verify_false h tight cert

def blocked (k q : Nat) (T : Table) (ws : List AugWire) : Bool :=
  let cols := (ws.map Prod.fst).dedup
  if !(cover ws true && cover ws false && decide (cols.length≤k+1) && unionSep false cols==top)
    then true
  else if k==0 then !(ws.any baseWire)
  else matched T q ws || (cols.length==k+1 && rectCheck cols)

theorem blocked_false {k q T ws} (val : Valid k T) (run : Shadow k q ws.toFinset) :
    blocked k q T ws=false := by
  have facts := local_of run
  let cols := (ws.map Prod.fst).dedup
  have same : cols.toFinset=ws.toFinset.image Prod.fst := by ext w; simp [cols]
  have h : Live k 0 cols.toFinset := by rw [same]; exact facts.live
  have card := List.toFinset_card_of_nodup (List.nodup_dedup (ws.map Prod.fst))
  have width := ProtocolProof.width h
  have bound : cols.length ≤ k+1 := by change cols.toFinset.card=cols.length at card; omega
  have cov : unionSep false cols=top := live_cover h rfl
  have both (s : Bool) : cover ws s=true := by
    obtain ⟨x,hx,hc⟩ := facts.caps s
    exact List.any_eq_true.mpr ⟨x,List.mem_toFinset.mp hx,hc⟩
  have body : (cover ws true && cover ws false && decide (cols.length≤k+1) && unionSep false cols==top)=true := by
    rw [both,both,cov]; simp [bound]
  unfold blocked
  change (if !(cover ws true && cover ws false && decide (cols.length≤k+1) && unionSep false cols==top)
    then true else if k==0 then !(ws.any baseWire) else matched T q ws || (cols.length==k+1 && rectCheck cols))=false
  rw [body]
  by_cases ez : k=0
  · subst k
    obtain ⟨u,hu,hb⟩ := zero_member run
    have yes : ws.any baseWire=true := List.any_eq_true.mpr ⟨u,List.mem_toFinset.mp hu,hb⟩
    simp [yes]
  · have ct : (cols.length==k+1 && rectCheck cols)=false := by
      apply Bool.eq_false_iff.mpr
      intro fail
      simp only [Bool.and_eq_true,beq_iff_eq] at fail
      exact Bool.false_ne_true ((rectCheck_false h (by change cols.toFinset.card=cols.length at card; omega)).symm.trans fail.2)
    simp [ez,matched_false val run,ct]

def leftOver (xs : List AugWire) (a b : AugWire) (ka kb : Bool) :=
  xs.filter fun v => (v != a || ka) && (v != b || kb)

theorem leftOver_set {ws : List AugWire} {U : Finset AugWire} {a b : AugWire}
    (sub : ws.toFinset=insert a (insert b U)) :
    (leftOver ws a b (decide (a∈U)) (decide (b∈U))).toFinset=U := by
  ext x
  have mem : x∈ws ↔ x=a ∨ x=b ∨ x∈U := by rw [←List.mem_toFinset,sub]; simp
  simp only [List.mem_toFinset,List.mem_filter,leftOver,Bool.and_eq_true,Bool.or_eq_true,
    bne_iff_ne,decide_eq_true_eq,mem]
  by_cases xa : x=a <;> by_cases xb : x=b <;> subst_vars <;> aesop

def one (k q : Nat) (T : Table) (ws : List AugWire) (a b : AugWire) (d : Bool) :=
  let z := augGate d a b
  decide (augPay d a b≤q) && z.1 != zero && z.1 != CoAO3143.one &&
    !(rawKW.contains z.1) && !(ws.any fun w => w.1==z.1) &&
      options.any fun ka => options.any fun kb =>
        !(blocked k (q-augPay d a b) T (z::leftOver ws a b ka kb))

def node (k q : Nat) (T : Table) (ws : List AugWire) : Bool :=
  !(scanPairs (fun a b => options.any (one k q T ws a b)) ws)

private theorem flag_comm (d : Bool) (a b : Flag) : mergeFlag d a b=mergeFlag d b a := by
  cases d <;> simp [mergeFlag,Bool.and_comm,Bool.or_comm]

theorem aug_comm (d : Bool) (a b : AugWire) : augGate d a b=augGate d b a := by
  cases d <;> simp [augGate,bin,mergePair,flag_comm,BitVec.or_comm,BitVec.and_comm]

theorem pay_comm (d : Bool) (a b : AugWire) : augPay d a b=augPay d b a := by
  simp [augPay,Bool.or_comm]

private theorem one_found {k q T ws U d a b}
    (val : Valid k T) (sub : ws.toFinset=insert a (insert b U))
    (bd : augPay d a b≤q) (pr : proper (augGate d a b).1)
    (nu : (augGate d a b).1∉ws.toFinset.image Prod.fst)
    (nr : (augGate d a b).1∉rawKW)
    (child : Shadow k (q-augPay d a b) (insert (augGate d a b) U)) :
    (options.any (one k q T ws a b))=true := by
  apply List.any_eq_true.mpr
  refine ⟨d,all_options _,?_⟩
  have no : (ws.any fun w => w.1==(augGate d a b).1)=false := by
    apply Bool.eq_false_iff.mpr
    intro bad
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp bad
    exact nu (Finset.mem_image.mpr ⟨x,List.mem_toFinset.mpr hx,beq_iff_eq.mp he⟩)
  have en : (decide (augPay d a b≤q) && (augGate d a b).1!=zero &&
      (augGate d a b).1!=CoAO3143.one && !(rawKW.contains (augGate d a b).1) &&
      !(ws.any fun w => w.1==(augGate d a b).1))=true := by
    simp [bd,pr.1,pr.2,nr,no]
  change (_ && options.any (fun ka => options.any (fun kb =>
    !(blocked k (q-augPay d a b) T (augGate d a b::leftOver ws a b ka kb)))))=true
  rw [en,Bool.true_and]
  apply List.any_eq_true.mpr
  refine ⟨decide (a∈U),all_options _,List.any_eq_true.mpr ⟨decide (b∈U),all_options _,?_⟩⟩
  have tail : Shadow k (q-augPay d a b)
      ((augGate d a b)::leftOver ws a b (decide (a∈U)) (decide (b∈U))).toFinset := by
    simpa [leftOver_set sub] using child
  simp [blocked_false val tail]

theorem node_ok {k q T ws} (val : Valid k T) (verified : node k q T ws=true) :
    ¬ Shadow (k+1) q ws.toFinset := by
  intro h
  generalize hs : ws.toFinset = S at h
  cases h with
  | step d a b ne bd pr nu nr facts child =>
    have ha : a∈ws := by rw [←List.mem_toFinset,hs]; simp
    have hb : b∈ws := by rw [←List.mem_toFinset,hs]; simp
    have unused : (augGate d a b).1∉ws.toFinset.image Prod.fst := by rwa [hs]
    have H := one_found val hs bd pr unused nr child
    have hs' : ws.toFinset=insert b (insert a _) := hs.trans (Finset.insert_comm _ _ _)
    have Q := one_found (k:=k) (q:=q) (d:=d) val hs' (by rwa [pay_comm d b a]) (by rwa [aug_comm d b a])
      (by rwa [aug_comm d b a]) (by rwa [aug_comm d b a])
      (by rwa [pay_comm d b a,aug_comm d b a])
    have yes := scanPairs_complete (fun a b => options.any (one k q T ws a b)) ha hb ne H Q
    simpa [node,yes] using verified

end CoNum4358.RectCheck
