import PEqualNP.CoAO3143Restriction

namespace CoChoice3456
open CoAO3143Restriction

structure Step (α : Type) where
  join : Bool
  left : Wire α
  right : Wire α

def Step.value {α} (g : Step α) : Wire α := op g.join g.left g.right
def reads {α} (g : Step α) (v : Wire α) : Prop := g.left=v ∨ g.right=v

def registered {α} (bank : List (Wire α)) : List (Step α) → Prop
  | [] => True
  | g :: gs => g.left∈bank ∧ g.right∈bank ∧ registered (g.value::bank) gs

def wires {α} (bank : List (Wire α)) : List (Step α) → List (Wire α)
  | [] => bank
  | g::gs => wires (g.value::bank) gs

noncomputable section
local instance {β} (v : Wire β) : Decidable (Constant v) := Classical.propDecidable _

def stepCost {α β} (f : β→α) (g : Step α) : Nat :=
  if Constant (cut f g.left) ∨ Constant (cut f g.right) then 0 else 1

def price {α β} (f : β→α) : List (Step α) → Nat
  | [] => 0
  | g::gs => stepCost f g + price f gs

private theorem absorb_constant {β} {a b : Wire β} (d : Bool)
    (h : Constant a ∨ Constant b) :
    Constant (op d a b) ∨ op d a b=a ∨ op d a b=b := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases d <;> cases v
    · exact Or.inl ⟨false,by funext r; simp [op,con]⟩
    · exact Or.inr (Or.inr (by funext r; simp [op,con]))
    · exact Or.inr (Or.inr (by funext r; simp [op,con]))
    · exact Or.inl ⟨true,by funext r; simp [op,con]⟩
  · cases d <;> cases v
    · exact Or.inl ⟨false,by funext r; simp [op,con]⟩
    · exact Or.inr (Or.inl (by funext r; simp [op,con]))
    · exact Or.inr (Or.inl (by funext r; simp [op,con]))
    · exact Or.inl ⟨true,by funext r; simp [op,con]⟩

/-- Charge exactly one abstract step per gate with two nonconstant restricted arguments. -/
theorem replay {α β : Type} (f : β→α) (raw : List (Wire β)) (gs : List (Step α))
    {old : List (Wire α)} (ok : registered old gs)
    {k : Nat} {bank : List (Wire β)} (built : Build raw k bank)
    (cs : ∀ b : Bool, con b∈bank) (rep : ∀ v∈old, cut f v∈bank) :
    ∃ pool, Build raw (k+price f gs) pool ∧ ∀ v∈wires old gs, cut f v∈pool := by
  classical
  induction gs generalizing old k bank with
  | nil => exact ⟨bank,by simpa [price] using built,rep⟩
  | cons g gs ih =>
    obtain ⟨hl,hr,hnext⟩ := ok
    have al := rep g.left hl
    have ar := rep g.right hr
    have val : cut f g.value=op g.join (cut f g.left) (cut f g.right) := rfl
    by_cases fixed : Constant (cut f g.left) ∨ Constant (cut f g.right)
    · have now : cut f g.value ∈ bank := by
        rw [val]
        rcases absorb_constant g.join fixed with ⟨b,eq⟩|eq|eq
        · rw [eq]; exact cs b
        · rw [eq]; exact al
        · rw [eq]; exact ar
      obtain ⟨pool,hp,hw⟩ := ih hnext built cs (by
        intro v hv
        rcases List.mem_cons.mp hv with rfl|rest
        · exact now
        · exact rep v rest)
      exact ⟨pool,by simpa [price,stepCost,fixed] using hp,hw⟩
    · have next : Build raw (k+1) (cut f g.value::bank) :=
        Build.gate built g.join _ _ al ar
      obtain ⟨pool,hp,hw⟩ := ih hnext next (fun b => List.mem_cons_of_mem _ (cs b)) (by
        intro v hv
        rcases List.mem_cons.mp hv with rfl|rest
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (rep v rest))
      refine ⟨pool,?_,hw⟩
      have size : k+price f (g::gs)=k+1+price f gs := by simp [price,stepCost,fixed,Nat.add_assoc]
      rwa [size]

private theorem price_le {α β} (f : β→α) (gs : List (Step α)) : price f gs ≤ gs.length := by
  induction gs with
  | nil => exact Nat.le_refl _
  | cons g gs ih =>
    simp only [price,List.length_cons,stepCost]
    split <;> omega

private theorem price_add {α β} (f : β→α) (gs hs : List (Step α)) :
    price f (gs++hs) = price f gs+price f hs := by
  induction gs with
  | nil => simp [price]
  | cons g gs ih => simp [price,ih,Nat.add_assoc]

private theorem read_free {α β} (f : β→α) (g : Step α) {w : Wire α}
    (hr : reads g w) (hc : Constant (cut f w)) : stepCost f g=0 := by
  apply if_pos
  rcases hr with h | h
  · exact Or.inl (h.symm ▸ hc)
  · exact Or.inr (h.symm ▸ hc)

/-- A binary AND absorbs false and a binary OR absorbs true. In the chosen
    phase the gate itself and any later consumer have zero restricted cost. -/
theorem reader_absorbs {α β} (f : β→α) (g : Step α) {y : Wire α}
    (rd : reads g y) (fixed : cut f y = con g.join) : cut f g.value=con g.join := by
  apply funext
  intro r
  have hv := congrFun fixed r
  change y (f r)=g.join at hv
  rcases g with ⟨d,a,b⟩
  rcases rd with e|e
  · change a=y at e
    subst a
    cases d <;> simp_all [Step.value,cut,op,con]
  · change b=y at e
    subst b
    cases d <;> simp_all [Step.value,cut,op,con]

theorem choose_two {α β} (lift : Bool→β→α) (y : Wire α)
    (sets : ∀ b : Bool, cut (lift b) y=con b)
    (pre mid post : List (Step α)) (g h : Step α) (readY : reads g y) (readGate : reads h g.value) :
    price (lift g.join) (pre++g::(mid++h::post))+2 ≤ (pre++g::(mid++h::post)).length := by
  let f := lift g.join
  have cg := read_free f g readY ⟨g.join,sets _⟩
  have ch := read_free f h readGate ⟨g.join,reader_absorbs f g readY (sets _)⟩
  change price f _+2≤_
  simp only [price_add,price,cg,ch,zero_add,List.length_append,List.length_cons]
  have hp := price_le f pre
  have hm := price_le f mid
  have hq := price_le f post
  omega

private theorem split_member {α : Type} {a : α} {xs : List α} (mem : a∈xs) :
    ∃ l r, xs=l++a::r := by
  induction xs with
  | nil => simp at mem
  | cons v vs ih =>
    rcases List.mem_cons.mp mem with rfl | h
    · exact ⟨[],vs,rfl⟩
    · obtain ⟨l,r,eq⟩ := ih h
      exact ⟨v::l,r,by simp [eq]⟩

def stable {α β} (lift : Bool→β→α) (w : Wire α) := cut (lift false) w=cut (lift true) w

private theorem two_stable {α β} (lift : Bool→β→α) (g : Step α)
    (hl : stable lift g.left) (hr : stable lift g.right) : stable lift g.value := by
  change op g.join (cut (lift false) g.left) (cut (lift false) g.right) =
      op g.join (cut (lift true) g.left) (cut (lift true) g.right)
  rw [hl,hr]

private def pending {α β} (lift : Bool→β→α) (y : Wire α) (gs : List (Step α)) (w : Wire α) :=
  stable lift w ∨ w=y ∨ ((∃ b : Bool, Constant (cut (lift b) w)) ∧ ∀ h∈gs, ¬reads h w)

private theorem reader_pair_aux {α β} (lift : Bool→β→α) (y : Wire α)
    (sets : ∀ b : Bool, cut (lift b) y=con b) (out : Wire α)
    (dep : ¬stable lift out) (non : ∀ b : Bool, ¬Constant (cut (lift b) out))
    (gs : List (Step α)) {bank : List (Wire α)} (reg : registered bank gs)
    (seed : ∀ w∈bank, pending lift y gs w) (hit : out∈wires bank gs) :
    ∃ pre g mid h post, gs=pre++g::(mid++h::post) ∧ reads g y ∧ reads h g.value := by
  classical
  induction gs generalizing bank with
  | nil =>
    rcases seed out hit with st | eq | ⟨⟨b,hb⟩,_⟩
    · exact (dep st).elim
    · rw [eq] at non
      exact (non false ⟨false,sets false⟩).elim
    · exact (non b hb).elim
  | cons g gs ih =>
    obtain ⟨hl,hr,tail⟩ := reg
    by_cases pair : reads g y ∧ ∃ h∈gs, reads h g.value
    · obtain ⟨rd,h,mem,use⟩ := pair
      obtain ⟨mid,post,e⟩ := split_member mem
      exact ⟨[],g,mid,h,post,by simp [e],rd,use⟩
    · have old w (hw : w∈bank) : pending lift y gs w := by
        rcases seed w hw with st | eq | ⟨b,unused⟩
        · exact Or.inl st
        · exact Or.inr (Or.inl eq)
        · exact Or.inr (Or.inr ⟨b,fun h hh => unused h (List.mem_cons_of_mem _ hh)⟩)
      have new : pending lift y gs g.value := by
        by_cases rd : reads g y
        · refine Or.inr (Or.inr ⟨⟨g.join,g.join,reader_absorbs (lift _) g rd (sets _)⟩,?_⟩)
          exact fun h mem use => pair ⟨rd,h,mem,use⟩
        · have get (w) (hw : w∈bank) (read : reads g w) : stable lift w := by
            rcases seed w hw with st | eq | ⟨_,no⟩
            · exact st
            · exact (rd (eq ▸ read)).elim
            · exact (no g List.mem_cons_self read).elim
          exact Or.inl (two_stable lift g (get g.left hl (Or.inl rfl)) (get g.right hr (Or.inr rfl)))
      obtain ⟨pre,q,mid,h,post,e,a,b⟩ := ih tail (by
        intro w hw
        rcases List.mem_cons.mp hw with rfl|mem
        · exact new
        · exact old w mem) hit
      exact ⟨g::pre,q,mid,h,post,by simp [e],a,b⟩

/-- The existence of a direct reader and a later gate using its value follows
    from essentiality and exclusion of constant cofactors, without a liveness
    or minimality assumption on the trace. -/
theorem choose_two_for_output {α β} (lift : Bool→β→α) (y out : Wire α)
    (sets : ∀ b : Bool, cut (lift b) y=con b)
    (dep : ¬stable lift out) (non : ∀ b : Bool, ¬Constant (cut (lift b) out))
    {bank : List (Wire α)} (gs : List (Step α)) (reg : registered bank gs)
    (seed : ∀ w∈bank, w=y ∨ stable lift w) (hit : out∈wires bank gs) :
    ∃ b : Bool, price (lift b) gs + 2 ≤ gs.length := by
  obtain ⟨pre,g,mid,h,post,e,ry,rg⟩ := reader_pair_aux lift y sets out dep non gs reg
    (fun w hw => (seed w hw).elim (fun e => Or.inr (Or.inl e)) Or.inl) hit
  refine ⟨g.join,?_⟩
  rw [e]
  exact choose_two lift y sets pre mid post g h ry rg

theorem chosenReplay {α β} (lift : Bool→β→α) (y out : Wire α)
    (sets : ∀ b : Bool, cut (lift b) y=con b) (dep : ¬stable lift out)
    (non : ∀ b : Bool, ¬Constant (cut (lift b) out))
    {bank : List (Wire α)} (gs : List (Step α)) (reg : registered bank gs)
    (seed : ∀ w∈bank, w=y ∨ stable lift w) (hit : out∈wires bank gs)
    (new : List (Wire β)) (cs : ∀ b : Bool, con b∈new)
    (base : ∀ b : Bool, ∀ w∈bank, cut (lift b) w∈new) :
    ∃ b : Bool, ∃ m pool, Build new m pool ∧ cut (lift b) out∈pool ∧ m+2 ≤ gs.length := by
  obtain ⟨b,hb⟩ := choose_two_for_output lift y out sets dep non gs reg seed hit
  obtain ⟨pool,built,present⟩ := replay (lift b) new gs reg (Build.start (raw:=new)) cs (base b)
  exact ⟨b,price (lift b) gs,pool,by simpa using built,present out hit,hb⟩

/-- On a core input for which K is false and r true, the pendant path value
    copies x, for both phases of y. Removing x recovers K for every core row. -/
def path {α : Type} (K attach : Wire α) (r : α) (x y : Bool) :=
  K r || (x && (attach r || y))

theorem path_cofactor {α} (K attach : Wire α) {w : α} (off : K w=false)
    (on_ : attach w=true) :
    (∀ b : Bool, path K attach w false b=false ∧ path K attach w true b=true) ∧
    (∀ r : α, ∀ b : Bool, path K attach r false b=K r) := by
  simp [path,off,on_]


def setLeaf {α : Type} (b : Bool) (u : α × Bool) := (u,b)
def leaf {α : Type} (u : (α × Bool) × Bool) := u.2
def pendant {α : Type} (K attach : Wire α) (u : (α × Bool) × Bool) :=
  path K attach u.1.1 u.1.2 u.2

theorem pathEligibility {α : Type} (K attach : Wire α) {a r : α}
    (ka : K a=false) (ra : attach a=false) (kr : K r=false) (rr : attach r=true) :
    ¬stable setLeaf (pendant K attach) ∧
    ∀ b : Bool, ¬Constant (cut (setLeaf b) (pendant K attach)) := by
  constructor
  · intro h
    have e := congrFun h (a,true)
    simpa [cut,setLeaf,pendant,path,ka,ra] using e
  · rintro b ⟨v,h⟩
    have neg := congrFun h (r,false)
    have pos := congrFun h (r,true)
    simp [cut,setLeaf,pendant,path,kr,rr,con] at neg pos
    cases v <;> simp_all

theorem pathChoice {α : Type} (K attach : Wire α) {a r : α}
    (ka : K a=false) (ra : attach a=false) (kr : K r=false) (rr : attach r=true)
    {raw : List (Wire ((α × Bool) × Bool))} (gs : List (Step ((α × Bool) × Bool)))
    (reg : registered raw gs) (seed : ∀ w∈raw, w=leaf ∨ stable setLeaf w)
    (hit : pendant K attach∈wires raw gs) :
    ∃ b : Bool, price (setLeaf b) gs + 2 ≤ gs.length := by
  obtain ⟨dep,both⟩ := pathEligibility K attach ka ra kr rr
  exact choose_two_for_output setLeaf leaf (pendant K attach) (fun _ => rfl) dep both gs reg seed hit


private theorem wires_append {α : Type} (bank : List (Wire α)) (xs ys : List (Step α)) :
    wires bank (xs++ys)=wires (wires bank xs) ys := by
  induction xs generalizing bank with
  | nil => rfl
  | cons g xs ih => exact ih _

private theorem register_append {α : Type} (xs ys : List (Step α)) {bank : List (Wire α)}
    (a : registered bank xs) (b : registered (wires bank xs) ys) : registered bank (xs++ys) := by
  induction xs generalizing bank with
  | nil => exact b
  | cons g xs ih => exact ⟨a.1,a.2.1,ih a.2.2 b⟩

theorem traceOfBuild {α : Type} {bank pool : List (Wire α)} {n} (h : Build bank n pool) :
    ∃ gs : List (Step α), gs.length=n ∧ registered bank gs ∧ wires bank gs=pool := by
  induction h with
  | start => exact ⟨[],rfl,trivial,rfl⟩
  | @gate k xs pre d a b ha hb ih =>
    obtain ⟨gs,len,reg,eq⟩ := ih
    let g : Step _ := ⟨d,a,b⟩
    refine ⟨gs++[g],by simp [len],register_append _ _ reg ?_,?_⟩
    · rw [eq]
      exact ⟨ha,hb,trivial⟩
    · rw [wires_append,eq]
      rfl

private theorem direct_reader {α β} (lift : Bool→β→α) (y out : Wire α)
    (dep : ¬stable lift out) (ne : out≠y) (gs : List (Step α))
    {bank : List (Wire α)} (reg : registered bank gs)
    (seed : ∀ w∈bank, w=y ∨ stable lift w) (hit : out∈wires bank gs) :
    ∃ g∈gs, reads g y := by
  induction gs generalizing bank with
  | nil => exact ((seed out hit).elim ne dep).elim
  | cons g gs ih =>
    obtain ⟨hl,hr,ht⟩ := reg
    by_cases use : reads g y
    · exact ⟨g,List.mem_cons_self,use⟩
    · have sl := (seed g.left hl).resolve_left (fun e => use (Or.inl e))
      have sr := (seed g.right hr).resolve_left (fun e => use (Or.inr e))
      obtain ⟨h,hm,hy⟩ := ih ht (by
        intro w hw
        rcases List.mem_cons.mp hw with rfl|hw
        · exact Or.inr (two_stable lift g sl sr)
        · exact seed w hw) hit
      exact ⟨h,List.mem_cons_of_mem _ hm,hy⟩

/-- Unlike the two-gate theorem, this one allows the phase to be prescribed.
    Only the other input dependence and nontriviality of the target are needed. -/
theorem fixedReplay {α β} (lift : Bool→β→α) (y out : Wire α) (b : Bool)
    (fix : cut (lift b) y=con b) (dep : ¬stable lift out) (ne : out≠y)
    {bank pool : List (Wire α)} {k : Nat} (build : Build bank k pool)
    (seed : ∀ w∈bank,w=y ∨ stable lift w) (hit : out∈pool)
    (new : List (Wire β)) (cs : ∀ t : Bool, con t∈new)
    (base : ∀ w∈bank, cut (lift b) w∈new) :
    ∃ m ws, Build new m ws ∧ cut (lift b) out∈ws ∧ m+1≤k := by
  obtain ⟨gs,length,reg,eq⟩ := traceOfBuild build
  have actual : out∈wires bank gs := eq.symm ▸ hit
  obtain ⟨g,mem,use⟩ := direct_reader lift y out dep ne gs reg seed actual
  obtain ⟨l,r,e⟩ := split_member mem
  have saved : price (lift b) gs+1 ≤ k := by
    rw [←length,e]
    have zero := read_free (lift b) g use ⟨b,fix⟩
    simp only [price_add,price,zero,zero_add,List.length_append,List.length_cons]
    have hl := price_le (lift b) l
    have hr := price_le (lift b) r
    omega
  obtain ⟨xs,run,hx⟩ := replay (lift b) new gs reg (Build.start (raw:=new)) cs base
  exact ⟨price (lift b) gs,xs,by simpa using run,hx out actual,saved⟩

def setInner {α : Type} (b : Bool) (r : α) := (r,b)
def inner {α : Type} (v : α × Bool) := v.2

theorem pendantReplay {α : Type} (K attach : Wire α) {a r t : α}
    (ka : K a=false) (ra : attach a=false) (kr : K r=false) (rr : attach r=true)
    (kt : K t=true) {bank pool : List (Wire ((α × Bool) × Bool))} {k : Nat}
    (build : Build bank k pool) (src : ∀ w∈bank, w=leaf ∨ stable setLeaf w)
    (hit : pendant K attach∈pool) (mid : List (Wire (α×Bool))) (endBank : List (Wire α))
    (mc : ∀ b : Bool, con b∈mid) (ec : ∀ b : Bool, con b∈endBank)
    (mraw : ∀ b : Bool, ∀ w∈bank, cut (setLeaf b) w∈mid)
    (ms : ∀ w∈mid,w=inner ∨ stable setInner w)
    (eraw : ∀ w∈mid, cut (setInner false) w∈endBank) :
    ∃ m ws, Build endBank m ws ∧ K∈ws ∧ m+3≤k := by
  obtain ⟨gs,len,reg,vals⟩ := traceOfBuild build
  obtain ⟨dep,both⟩ := pathEligibility K attach ka ra kr rr
  obtain ⟨b,n,ys,pr,live,saved⟩ := chosenReplay setLeaf leaf (pendant K attach) (fun _ => rfl)
    dep both gs reg src (vals.symm ▸ hit) mid mc mraw
  let out := cut (setLeaf b) (pendant K attach)
  have depends : ¬stable setInner out := by
    intro e
    have bad := congrFun e r
    simpa [out,cut,setInner,setLeaf,pendant,path,kr,rr] using bad
  have other : out≠inner := by
    intro e
    have bad := congrFun e (t,false)
    simpa [out,cut,setLeaf,pendant,path,kt,inner] using bad
  obtain ⟨m,ws,prog,has,budget⟩ :=
    fixedReplay setInner inner out false rfl depends other pr ms live endBank ec eraw
  have equals : cut (setInner false) out=K := by
    funext w
    simp [cut,out,setInner,setLeaf,pendant,path]
  exact ⟨m,ws,prog,equals ▸ has,by omega⟩

end
end CoChoice3456
