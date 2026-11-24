import PEqualNP.CoAO3143Cotree
import PEqualNP.CoAO3143RectangleSearch

namespace CoAO3143.Cotree
open ProtocolProof

structure Link where
  a : Sig
  b : Sig
  fixed : Row
  i : Row
  j : Row

def linkOK (ws : List Sig) (d : Bool) (e : Link) : Bool :=
  if d then forcedB ws e.fixed e.i e.a && forcedB ws e.fixed e.j e.b
  else forcedB ws e.i e.fixed e.a && forcedB ws e.j e.fixed e.b

private theorem answer_forced (t : ReadTree) (ws : List Sig) (v : t.value=target)
    (leaves : t.sources=ws.toFinset) (p n : Row) (a : Sig) (h : forcedB ws p n a=true) :
    answer p n t=a := by
  have ht : separates p n t.value := by
    rw [v]
    constructor
    · change (BitVec.allOnes 160).getLsbD p.val = true
      rw [BitVec.getLsbD_allOnes]
      simp
    · simp [bit,target]
  have valid := answer_valid p n t ht
  have member : answer p n t∈ws := List.mem_toFinset.mp (leaves ▸ answer_mem p n t)
  have ok := List.all_eq_true.mp h _ member
  rcases valid with ⟨hp,hn⟩
  simpa [hp,hn] using ok

private theorem link_works (t : ReadTree) (ws : List Sig) (value : t.value=target)
    (leaves : t.sources=ws.toFinset) (d : Bool) (e : Link) (h : linkOK ws d e=true) :
    Together t d e.a e.b := by
  refine ⟨e.fixed,e.i,e.j,?_⟩
  cases d <;> simp only [linkOK,Bool.false_eq_true,↓reduceIte,Bool.and_eq_true] at h ⊢ <;>
    exact ⟨answer_forced t ws value leaves _ _ _ h.1,answer_forced t ws value leaves _ _ _ h.2⟩

def spanCheck (ws nodes : List Sig) (d : Bool) : List Sig → List Link → Bool
  | seen, [] => nodes.all seen.contains
  | seen, e::edges => seen.contains e.a && nodes.contains e.b && linkOK ws d e &&
      spanCheck ws nodes d (e.b::seen) edges

private theorem span_const (t : ReadTree) (ws nodes : List Sig) (value : t.value=target)
    (leaves : t.sources=ws.toFinset) (d : Bool) (anchor : Sig) (f : Sig→Bool)
    (unchanged : ∀ a∈nodes,∀ b∈nodes,Together t d a b → f a=f b) (edges : List Link)
    (seen : List Sig) (known : ∀ a∈seen, a∈nodes ∧ f a=f anchor)
    (check : spanCheck ws nodes d seen edges=true) : ∀ a∈nodes, f a=f anchor := by
  induction edges generalizing seen with
  | nil =>
    intro a ha
    have found := List.all_eq_true.mp check a ha
    exact (known a (by simpa using found)).2
  | cons e es ih =>
    simp only [spanCheck,Bool.and_eq_true] at check
    obtain ⟨⟨⟨sa,sb⟩,edge⟩,rest⟩ := check
    have za := known e.a (by simpa using sa)
    have zb : e.b∈nodes := by simpa using sb
    have move := unchanged e.a za.1 e.b zb (link_works t ws value leaves _ _ edge)
    apply ih (e.b::seen) _ rest
    intro a ha
    rcases List.mem_cons.mp ha with rfl | old
    · exact ⟨zb,move.symm.trans za.2⟩
    · exact known a old

structure Obstruction where
  seed : Sig
  other : Sig
  extra : List Sig
  positive : List Link
  negative : List Link

def Obstruction.nodes (o : Obstruction) := o.seed::o.other::o.extra

def verifyTree (ws : List Sig) (o : Obstruction) : Bool :=
  o.seed != o.other && o.nodes.all ws.contains &&
  spanCheck ws o.nodes true [o.seed] o.positive &&
  spanCheck ws o.nodes false [o.seed] o.negative

theorem verify_false {k ws} (live : Live k 0 ws.toFinset) (tight : ws.toFinset.card=k+1)
    (o : Obstruction) : verifyTree ws o=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [verifyTree,Bool.and_eq_true,bne_iff_ne] at h
  obtain ⟨⟨⟨ne,sub⟩,red⟩,blue⟩ := h
  obtain ⟨t,val,lin,src⟩ := tight_tree live rfl (by omega)
  have seed : o.seed∈o.nodes := List.mem_cons_self
  have other : o.other∈o.nodes := List.mem_cons_of_mem _ List.mem_cons_self
  have subset : o.nodes.toFinset ⊆ t.sources := by
    intro w hw
    rw [src,List.mem_toFinset]
    have m := List.all_eq_true.mp sub w (List.mem_toFinset.mp hw)
    simpa using m
  apply ne
  apply incompatible t lin o.nodes.toFinset subset _ (List.mem_toFinset.mpr seed) (List.mem_toFinset.mpr other)
  intro d f edges a ha b hb
  have localEdge : ∀ x∈o.nodes,∀ y∈o.nodes,Together t d x y→f x=f y :=
    fun x hx y hy => edges x (List.mem_toFinset.mpr hx) y (List.mem_toFinset.mpr hy)
  have known : ∀ w∈[o.seed], w∈o.nodes ∧ f w=f o.seed := by
    intro w hw
    obtain rfl := List.mem_singleton.mp hw
    exact ⟨seed,rfl⟩
  have all : ∀ w∈o.nodes, f w=f o.seed := by
    cases d with
    | false => exact span_const t ws _ val src false o.seed f localEdge o.negative _ known blue
    | true => exact span_const t ws _ val src true o.seed f localEdge o.positive _ known red
  exact (all a (List.mem_toFinset.mp ha)).trans (all b (List.mem_toFinset.mp hb)).symm

/-- Propose concrete shared-row pairs. All claims are independently rechecked
    by linkOK, including both occurrences of the required unique labels. -/
def pairHint (g : Grid) (d : Bool) (x y : Profile) : Option Link :=
  let common := if d then x.pos &&& y.pos else x.neg &&& y.neg
  if common=0 then none else
  let idx := common.log2
  let band := ((if d then g.pos else g.neg)[idx]?).map (·.mask) |>.getD 0
  let opposite := fun u : B =>
    let cell := (band &&& u).toNat.log2
    if d then rowIndex (cell%g.stride) else rowIndex ((cell/g.stride)*g.stride)
  some ⟨x.wire,y.wire,if d then rowIndex (idx*g.stride) else rowIndex idx,
    opposite x.single,opposite y.single⟩

abbrev Span := List Profile × List Link

def sweep (g : Grid) (d : Bool) (all : List Profile) (s : Span) : Span :=
  all.foldl (fun st x =>
    if st.1.any (fun y => x.wire==y.wire) then st else
    match st.1.findSome? (fun y => pairHint g d y x) with
    | some e => (x::st.1,e::st.2)
    | none => st) s

def component (g : Grid) (d : Bool) (all : List Profile) : Nat → Span → Span
  | 0,s => s
  | n+1,s =>
    let m := sweep g d all s
    if m.1.length=s.1.length then s else component g d all n m

def complementOf (xs inside : List Profile) :=
  xs.filter fun x => !(inside.any fun y => x.wire==y.wire)

def findObstruction (g : Grid) : Nat → List Profile → Option Obstruction
  | 0,_ => none
  | n+1, x::y::rest =>
    let xs := x::y::rest
    let R := component g true xs xs.length ([x],[])
    if R.1.length≠xs.length then
      (findObstruction g n R.1).orElse fun _ => findObstruction g n (complementOf xs R.1)
    else
      let N := component g false xs xs.length ([x],[])
      if N.1.length≠xs.length then
        (findObstruction g n N.1).orElse fun _ => findObstruction g n (complementOf xs N.1)
      else some ⟨x.wire,y.wire,rest.map (·.wire),R.2.reverse,N.2.reverse⟩
  | _+1,_ => none

def cotreeReject (g : Grid) (ws : List Sig) : Bool :=
  let unique := (coverage false ws).2.1
  let ps := ws.map fun a =>
    let u := unique &&& sep false a
    {wire:=a,single:=u,pos:=axis u g.pos,neg:=axis u g.neg : Profile}
  (findObstruction g ws.length ps).any (verifyTree ws)

theorem cotree_false {k ws} (h : Live k 0 ws.toFinset) (tight : ws.toFinset.card=k+1) (g : Grid) :
    cotreeReject g ws=false := by
  unfold cotreeReject
  dsimp only
  generalize findObstruction g ws.length _ = est
  cases est with
  | none => rfl
  | some e => exact verify_false h tight e

def cotreeSearch (g : Grid) : Nat → Nat → List Sig → Bool
  | 0,_,ws => ws==[target]
  | k+1,t,ws => if (t==0 && ws.length==k+2) && cotreeReject g ws then false else
      stepTest k t ws (cotreeSearch g k (t-1)) (cotreeSearch g k t)

theorem cotree_complete {m t S} (h : Restricted m t S) (g : Grid) (k : Nat)
    (hk : m≤k) (v : List Sig) (hv : v.Nodup) (hs : v.toFinset=S) : cotreeSearch g k t v=true := by
  induction k generalizing m t S v with
  | zero => simpa [cotreeSearch,search] using search_complete h 0 hk v hv hs
  | succ k ih =>
    have skip : ((t==0 && v.length==k+2) && cotreeReject g v)=false := by
      apply Bool.eq_false_iff.mpr
      intro bad
      simp only [Bool.and_eq_true,beq_iff_eq] at bad
      obtain ⟨⟨rfl,len⟩,bad⟩ := bad
      subst S
      have sz := ProtocolProof.width h.live
      have card := List.toFinset_card_of_nodup hv
      exact Bool.false_ne_true ((cotree_false h.live (by omega) g).symm.trans bad)
    simp only [cotreeSearch,skip,Bool.false_eq_true,ite_false]
    apply reduced_step h hk hv hs <;>
      exact fun w hn l hl hh => ih hh hl w hn rfl

end CoAO3143.Cotree
