import PEqualNP.CoThetaGlue

set_option maxRecDepth 18000
set_option maxHeartbeats 0
namespace CoThetaCycleFive
open CoThetaFreeCore
open CoThetaBits (Wire Row den gate)
open CoThetaNine (SmallInput raw7 ans7 vertices7 pack unpack numeric_goal)
open CoThetaSeven (read_twice raw_mem)

def roots : List Wire := [
(0x7800ffe003ff800fffffc007ff001ffffffffffe003fffff001ffc007ff001ffc007ff001fffff800ffe003ffffffffffc007ff,0x520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a),
(0x7fff000003fffff001ffffffffffe003ff800fffffc007ffffe000007ffffe000007ffffe003ffffffffffc007ff001fffff800,0x604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c),
(0x3fffffffe000007fffffffc00000fffffffffffffffffff800000000007fffffffc00000ffffffff800001ffffffff,0x490921242484909212424849092124248490921242484909212424849092124248490921242484909212424849092124248490),
(0x7ffffffffc00000000000007fffffffffffff000000007fffffffffffffffffffff80000000000000fffffffffffffe00000000,0xe01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e0),
(0x7ffffffffffffffffffffff80000000000000000000007fffffffffffffffffffffffffffffffffff0000000000000000000000,0x700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700)]
def basis : CoNatBench.essentialBasis roots := CoThetaSix.basisAt_sound roots [4, 15, 1, 34, 90] (by decide +kernel)
theorem nd : roots.Nodup := by decide +kernel
theorem small : CoNatBench.guardedSearch 6 (roots.map CoNatBench.project)=false := by decide +kernel

def indexAt (v : Fin 7) : Option Nat := match v.val with
  | 0 => some 0 | 1 => some 1 | 2 => some 2 | 5 => some 3 | 6 => some 4 | _ => none

def column (vertex : Fin 7) : Wire := match indexAt vertex with
  | none => CoThetaBits.zero
  | some n => roots.getD n CoThetaBits.zero
def liftRows (r : Row) : SmallInput := pack (fun j => den (column j) r)

def cycleGraph : Wire :=
  gate .disj (gate .disj (gate .disj (gate .disj (gate .disj (gate .disj (gate .disj
    (gate .conj (column 0) (column 2)) (gate .conj (column 1) (column 2)))
    (gate .conj (column 0) (column 3))) (gate .conj (column 3) (column 4)))
    (gate .conj (column 1) (column 4))) (gate .conj (column 0) (column 5)))
    (gate .conj (column 5) (column 6))) (gate .conj (column 1) (column 6))


theorem table : cycleGraph=CoThetaBits.target := by decide +kernel

theorem input (j : Fin 7) : restrict liftRows (raw7 j)=den (column j) :=
  funext (fun r => unpack (fun v => den (column v) r) j)

theorem goal : restrict liftRows ans7=den CoThetaBits.target := by
  funext r
  change ans7 (liftRows r)=_
  rw [numeric_goal]
  have values : (fun j => raw7 j (liftRows r))=(fun j => den (column j) r) :=
    funext (fun j => congrFun (input j) r)
  rw [values]
  have equality := congrFun (congrArg den table) r
  simp only [cycleGraph,CoThetaBits.den_gate,applyKind] at equality
  exact equality

theorem known : ∀ w∈vertices7, restrict liftRows w∈absentBit::roots.map den := by
  intro w hw
  rcases List.mem_cons.mp hw with z|r
  · subst w
    exact List.mem_cons_self
  · obtain ⟨j,e⟩ := List.mem_ofFn.mp r
    subst w
    rw [input]
    cases h : indexAt j with
    | none => simp [column,h,CoThetaBits.den_zero]
    | some n =>
      cases hn : roots[n]? with
      | none => simp [column,h,List.getD_eq_getElem?_getD,hn,CoThetaBits.den_zero]
      | some v =>
        have inList := List.mem_map_of_mem (f:=den) (List.mem_of_getElem? hn)
        simp [column,h,List.getD_eq_getElem?_getD,hn,inList]

theorem residual {gs : List (TraceGate SmallInput)} (ok : sufficient vertices7 ans7 gs) :
    7≤remaining liftRows gs := by
  obtain ⟨ws,run,all⟩ := restrict_trace liftRows gs ok.1
    (Free.start (raw:=absentBit::roots.map den)) List.mem_cons_self known
  have h := all ans7 ok.2
  rw [goal] at h
  have yes := CoNatBench.table_bound basis nd run h small
  omega

def joint (a b : Bool) (j : Fin 32) : SmallInput :=
  pack (fun i => if i=3 then a else if i=4 then b else j.val.testBit ((indexAt i).getD 0))

theorem separation : ∀ a b c d : Bool, (a,b)≠(c,d) →
    ∃ j : Fin 32, ans7 (joint a b j)≠ans7 (joint c d j) := by decide +kernel

theorem panel_fixed (a b c d : Bool) (j : Fin 32) :
    agreeOutside (fun f => f=raw7 3 ∨ f=raw7 4) (joint a b j) (joint c d j) vertices7 := by
  intro f hf outside
  rcases List.mem_cons.mp hf with z|other
  · subst f
    rfl
  · obtain ⟨i,e⟩ := List.mem_ofFn.mp other
    subst f
    have i3 : i≠3 := fun e => outside (Or.inl (congrArg raw7 e))
    have i4 : i≠4 := fun e => outside (Or.inr (congrArg raw7 e))
    simp [joint,unpack,i3,i4]

def head : TraceGate SmallInput := ⟨.disj,raw7 3,raw7 4⟩

theorem no_live_ten {gs : List (TraceGate SmallInput)}
    (ok : sufficient vertices7 ans7 (head::gs)) (fresh : freshTrace vertices7 (head::gs))
    (budget : (head::gs).length≤10) :
    ∃ k ws, k≤gs.length ∧ Free vertices7 k ws ∧ ans7∈ws := by
  classical
  have h3 : reads head (raw7 3) := Or.inl rfl
  have h4 : reads head (raw7 4) := Or.inr rfl
  by_cases path : UsePath gs head.value ans7
  · exfalso
    have gone3 := (input 3).trans (show den (column 3)=absentBit from CoThetaBits.den_zero)
    have gone4 := (input 4).trans (show den (column 4)=absentBit from CoThetaBits.den_zero)
    have newp (g : TraceGate SmallInput) (hg : g∈head::gs) :
        g.value≠raw7 3 ∧ g.value≠raw7 4 :=
      ⟨fun e => fresh_outputs fresh g hg (e ▸ raw_mem 3),
       fun e => fresh_outputs fresh g hg (e ▸ raw_mem 4)⟩
    have head0 : restrict liftRows head.value=absentBit := by
      funext r
      change (raw7 3 (liftRows r) || raw7 4 (liftRows r))=false
      have a := congrFun gone3 r
      have b := congrFun gone4 r
      change raw7 3 (liftRows r)=false at a
      change raw7 4 (liftRows r)=false at b
      simp only [a,b,Bool.false_or]
    have nz : restrict liftRows ans7 ≠ absentBit := by
      rw [goal]
      intro e
      have bad := congrFun e (true,0)
      simp [CoThetaBits.den_target,absentBit] at bad
    obtain ⟨other,hm,n3,n4,drop⟩ := extra_loss_on_path liftRows gone3 gone4
      (fun g hg => newp g (List.mem_cons_of_mem _ hg)) path head0
      (newp head List.mem_cons_self) nz
    let all := head::gs
    let R := readerSet all (raw7 3) ∪ readerSet all (raw7 4)
    have card3 {a b c : TraceGate SmallInput} (ha : a∈R) (hb : b∈R) (hc : c∈R)
        (ab : a≠b) (ac : a≠c) (bc : b≠c) : 3≤R.card := by
      have sub : ({a,b,c}:Finset _) ⊆ R := by
        intro g hg
        simp only [Finset.mem_insert,Finset.mem_singleton] at hg
        rcases hg with rfl|rfl|rfl
        · exact ha
        · exact hb
        · exact hc
      have ct := Finset.card_le_card sub
      simpa [ab,ac,bc] using ct
    have from3 {g} (h : g∈all) (p : reads g (raw7 3)) : g∈R :=
      Finset.mem_union_left _ (mem_readerSet.mpr ⟨h,p⟩)
    have from4 {g} (h : g∈all) (p : reads g (raw7 4)) : g∈R :=
      Finset.mem_union_right _ (mem_readerSet.mpr ⟨h,p⟩)
    obtain ⟨A,ha,r3,ah⟩ := read_twice 3 4 (by decide) head h3 h4 ok
    obtain ⟨B,hb,r4,bh⟩ := read_twice 4 3 (by decide) head h4 h3 ok
    have three : 3≤R.card := by
      by_cases same : A=B
      · subst B
        have nraw (j : Fin 7) : ans7≠raw7 j := by
          obtain ⟨r,h⟩ := CoThetaSeven.seven_not_raw j
          exact fun e => h (congrFun e r)
        obtain ⟨row,ne⟩ := CoThetaSeven.seven_diff 3 4 (by decide)
        obtain ⟨C,hc,read,ch,ca⟩ := two_joint_readers_impossible (raw7 3) (raw7 4) ans7
          vertices7 all head A h3 h4 r3 r4 (fun e => ne (congrFun e row))
          ⟨nraw 3,nraw 4⟩ ok.1 ok.2 joint
          (fun a b j => by simp [joint,unpack])
          (fun a b j => by simp [joint,unpack]) panel_fixed separation
        exact card3 (from3 List.mem_cons_self h3) (from3 ha r3)
          (read.elim (from3 hc) (from4 hc)) ah.symm ch.symm ca.symm
      · exact card3 (from3 List.mem_cons_self h3) (from3 ha r3) (from4 hb r4)
          ah.symm bh.symm same
    have saved4 := four_saved_raw_head liftRows all (raw7 3) (raw7 4) gone3 gone4 three
      ⟨other,List.mem_cons_of_mem _ hm,n3,n4,drop⟩
    have cost := residual ok
    have eq := accounted liftRows (head::gs)
    change 4 ≤ saved liftRows (head::gs) at saved4
    omega
  · exact omit_dead_head vertices7 gs head.value ans7 ok.1.2.2 ok.2 path

end CoThetaCycleFive
namespace CoThetaFixedOrbit
open CoThetaFreeCore
open CoThetaNine (SmallInput raw7 ans7 vertices7)
open CoThetaSix (minorLift minor_off)
open CoThetaSeven (tag picked rotation numbered raw_mem rowPerm)

def rawGate (x y : Fin 7) (k : Kind) : TraceGate SmallInput := ⟨k,raw7 x,raw7 y⟩

theorem fresh_data (k : Kind) : ∀ (x y : Fin 7), x≠y →
    (∃ r : SmallInput, (rawGate x y k).value r ≠ false) ∧
    ∀ j : Fin 7, ∃ r : SmallInput, (rawGate x y k).value r ≠ raw7 j r := by
  cases k <;> decide +kernel

theorem head_fresh (x y : Fin 7) (k : Kind) (xy : x≠y) :
    (rawGate x y k).value∉vertices7 := by
  intro h
  rcases List.mem_cons.mp h with z|other
  · obtain ⟨r,off⟩ := (fresh_data k x y xy).1
    exact off (congrFun z r)
  · obtain ⟨j,eq⟩ := List.mem_ofFn.mp other
    obtain ⟨r,ne⟩ := (fresh_data k x y xy).2 j
    exact ne (congrFun eq.symm r)

def RawNine : Prop := ∃ n ws, n≤9 ∧ Free vertices7 n ws ∧ ans7∈ws
def PostNine (i : Fin 13) : Prop := ∃ n ws, n≤9 ∧ Free ((numbered i).value::vertices7) n ws ∧ ans7∈ws

theorem named_trace {x y : Fin 7} {k : Kind} (xy : x≠y)
    {n ws} (run : Free ((rawGate x y k).value::vertices7) n ws) (hit : ans7∈ws) :
    ∃ clean, sufficient vertices7 ans7 (rawGate x y k::clean) ∧
      freshTrace vertices7 (rawGate x y k::clean) ∧ clean.length≤n := by
  obtain ⟨ts,len,well,eq⟩ := trace_of_free run
  obtain ⟨clean,ok,fresh,le,_⟩ := simplify_trace ts ⟨well,eq ▸ hit⟩
  exact ⟨clean,⟨⟨raw_mem x,raw_mem y,ok.1⟩,ok.2⟩,⟨head_fresh x y k xy,fresh⟩,by omega⟩

theorem dispatch (x y : Fin 7) (k : Kind) (xy : x≠y) {n ws}
    (run : Free ((rawGate x y k).value::vertices7) n ws) (small : n≤9) (hit : ans7∈ws) :
    if tag x y k < 2 then RawNine else PostNine (picked (tag x y k)) := by
  classical
  let g := rawGate x y k
  obtain ⟨gs,ok,fresh,le⟩ := named_trace xy run hit
  change sufficient vertices7 ans7 (g::gs) at ok
  change freshTrace vertices7 (g::gs) at fresh
  have size : (g::gs).length≤10 := by simp only [List.length_cons]; omega
  have rx : reads g (raw7 x) := Or.inl rfl
  have ry : reads g (raw7 y) := Or.inr rfl
  let t := tag x y k
  change (if t<2 then _ else _)
  have rule := CoThetaSeven.dispatch_rules k x y xy
  change (if t=0 then _ else if t=1 then _ else _) at rule
  by_cases a : t=0
  · rw [if_pos a] at rule
    rw [if_pos (by omega : t<2)]
    have drop : restrict (minorLift x) g.value=absentBit := by
      funext r
      change applyKind k (raw7 x (minorLift x r)) (raw7 y (minorLift x r))=false
      have zero := congrFun (minor_off rule.1) r
      change raw7 x (minorLift x r)=false at zero
      rw [zero]
      exact rule.2 _
    obtain ⟨m,vs,sz,rest,out⟩ := CoThetaSeven.absorbing_head ok fresh size xy rx ry rule.1 drop
    exact ⟨m,vs,by omega,rest,out⟩
  · rw [if_neg a] at rule
    by_cases b : t=1
    · rw [if_pos b] at rule
      rw [if_pos (by omega : t<2)]
      have drop : restrict (minorLift y) g.value=absentBit := by
        funext r
        change applyKind k (raw7 x (minorLift y r)) (raw7 y (minorLift y r))=false
        have zero := congrFun (minor_off rule.1) r
        change raw7 y (minorLift y r)=false at zero
        rw [zero]
        exact rule.2 _
      obtain ⟨m,vs,sz,rest,out⟩ := CoThetaSeven.absorbing_head ok fresh size xy.symm ry rx rule.1 drop
      exact ⟨m,vs,by omega,rest,out⟩
    · rw [if_neg b] at rule
      rw [if_neg (by omega : ¬t<2)]
      let s := rotation t
      let i := picked t
      let pool := (numbered i).value::vertices7
      have eq : restrict (rowPerm s) g.value=(numbered i).value := funext rule
      have old : ∀ w∈g.value::vertices7, restrict (rowPerm s) w∈pool := by
        intro w hw
        rcases List.mem_cons.mp hw with z|h
        · subst w
          rw [eq]
          exact List.mem_cons_self
        rcases List.mem_cons.mp h with z|other
        · subst w
          exact List.mem_cons_of_mem _ List.mem_cons_self
        · obtain ⟨j,hj⟩ := List.mem_ofFn.mp other
          subst w
          rw [CoThetaSeven.raw_permute]
          exact List.mem_cons_of_mem _ (raw_mem _)
      obtain ⟨vs,newRun,sub⟩ := restrict_trace (rowPerm s) gs ok.1.2.2 (Free.start (raw:=pool))
        (List.mem_cons_of_mem _ List.mem_cons_self) old
      have goal := sub ans7 ok.2
      have unchanged : restrict (rowPerm s) ans7=ans7 := funext (CoThetaSeven.perm_graph s)
      rw [unchanged] at goal
      have account := accounted (rowPerm s) gs
      exact ⟨_,vs,by omega,newRun,goal⟩

end CoThetaFixedOrbit
namespace CoThetaCycleFive
open CoThetaNine (vertices7 ans7)
open CoThetaFreeCore
theorem no_post {n ws} (run : Free (head.value::vertices7) n ws)
    (bound : n≤9) (hit : ans7∈ws) : CoThetaFixedOrbit.RawNine := by
  obtain ⟨gs,ok,fresh,le⟩ := CoThetaFixedOrbit.named_trace (x:=3) (y:=4) (k:=.disj) (by decide) run hit
  have size : (head::gs).length≤10 := by simp only [List.length_cons]; omega
  obtain ⟨j,vs,small,prog,out⟩ := no_live_ten ok fresh size
  exact ⟨j,vs,by omega,prog,out⟩
end CoThetaCycleFive
