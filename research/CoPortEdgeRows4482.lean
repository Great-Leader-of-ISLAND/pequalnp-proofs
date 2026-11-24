import PEqualNP.CoPortRoots4482
import PEqualNP.CoBlockIntervals4482
namespace CoPortEdgeRows4482
open CoPortRoots4482 CoPortTrace4482 CoPortCut4482 CoBitBlock4482

/-- Each entry is a 9-bit input. The least significant entry is edge 0;
the row order is increasing lower endpoint, then increasing flipped input. -/
def lowCodes : Nat := 0x32592c964b2590c86432190c160b0582c16070381c0e070380c060301148a45229148a44a25128944a2110884420b0582c160b058241209048240a05028140a030180c06030080401a0d068341a0d064b2592c964b2190c86432182c160b0582c060301809249249249248241209045229148a45229128944a25128844221108241209048140a050280401d0e8743a1d0e070381c0e068341a0d06834190c86432190c06030180a8542a150a85028140a049249249249241209048229148a452291488442211082412090480401a0d068341a0c86432190c86430180c0602a150a8542a150a05028140a048241209048221108844221008040140a050281209048241008028140a050281209048241208040200a05028140a04020100402010040201
def highCodes : Nat := 0x3a5b2cd65b27d0d86632991e168b1586c1f074391c4e1707c0d06230994aa4d239168ad4a651a8b44ea1308c4470b4592c561b07c2512490c8350a450a8340e832188c26074090423a0f06c351a4d1e4ba5b2cd65f21d0d86632b82e168b1587c07031184d2592692c93582612891c5329549a4722f12a94ca3517885426118c25121906a148a1506a0425d1e87c3b1d6e0f03c1c8e368741e0d86a34d91c86c33196c0e031186a8d42e158ab502c148a349349649a4ba4160984aa2b14ca552691e88c42611a82612890e80429a2d078361acc964721d0d86730580e0632a551a8742e15ca15038160a648a4160984b22511884c239028042940e0582a520d058261808c28941a0702e12290c83417080c0310a250a8340e84060188406018842203
def endpoint (codes : Nat) (i : Row) : R :=
  ⟨(codes >>> (9*i.val)) % 512,Nat.mod_lt _ (by decide)⟩
def lower := endpoint lowCodes
def upper := endpoint highCodes
def flips : Nat := 0x653206532065320654321653276531065320653076543176531653206543165385321085421854218542185216532053208654208542185426520542152873108731087421087310871087310831085421842187543187318541818731087632087308764208742087310876208707310632030864208542184275431731620541
def flipped (i : Row) : Fin 9 := ⟨((flips >>> (4*i.val)) % 16) % 9,Nat.mod_lt _ (by decide)⟩

theorem one_flip : ∀ i : Row, (lower i).val.testBit (flipped i).val=false ∧
    (upper i).val=(lower i).val ||| 2^(flipped i).val := by decide +kernel

/-- These computations refer to the real project graph and original wires. -/
theorem labels : ∀ i : Row, label (lower i)=false ∧ label (upper i)=true := by decide +kernel
theorem raw_order : ∀ t : Fin 9, ∀ i : Row,
    cell (raw t) (lower i)=true → cell (raw t) (upper i)=true := by decide +kernel

def project (r : Row → R) (w : W) : Bits :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => cell w (r i)))).cast List.length_ofFn

theorem projected (r : Row → R) (w : W) (i : Row) :
    bit (project r w) i=cell w (r i) := by
  simp only [bit,project,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]

def mark (w : W) : Mark := (project upper w,project lower w)
theorem positive (w : W) (i : Row) : bit (mark w).1 i=cell w (upper i) := projected _ _ _
theorem negative (w : W) (i : Row) : bit (mark w).2 i=cell w (lower i) := projected _ _ _

theorem difference (w : W) (i : Row) :
    ((mark w).1 ^^^ (mark w).2).getLsbD i.val =
      (cell w (upper i) != cell w (lower i)) := by
  rw [BitVec.getLsbD_xor]
  change Bool.xor (bit (mark w).1 i) (bit (mark w).2 i)=_
  rw [positive,negative]
  cases cell w (upper i) <;> cases cell w (lower i) <;> rfl

private theorem proj_gate (r : Row→R) (d : Bool) (a b : W) :
    project r (join d a b)=if d then project r a ||| project r b else project r a &&& project r b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Row := ⟨j,hj⟩
  have V (w : W) : (project r w).getLsbD j=cell w (r i) := projected r w i
  cases d <;> simp only [Bool.false_eq_true,↓reduceIte,BitVec.getLsbD_and,BitVec.getLsbD_or,V,
    join,cell]

theorem mark_gate (d : Bool) (a b : W) : mark (join d a b)=
    if d then ((mark a).1 ||| (mark b).1,(mark a).2 ||| (mark b).2)
      else ((mark a).1 &&& (mark b).1,(mark a).2 &&& (mark b).2) := by
  cases d <;> simp only [mark,proj_gate,Bool.false_eq_true,↓reduceIte]

def Ordered (w : W) := ∀ i : Row,cell w (lower i)=true → cell w (upper i)=true

theorem join_ordered (d : Bool) {a b : W} (A : Ordered a) (B : Ordered b) :
    Ordered (join d a b) := by
  intro i
  cases d <;> simp only [join,cell,Bool.false_eq_true,↓reduceIte,BitVec.getLsbD_and,
    BitVec.getLsbD_or,Bool.and_eq_true,Bool.or_eq_true]
  · exact fun h => ⟨A i h.1,B i h.2⟩
  · exact fun h => h.imp (A i) (B i)

theorem start_ordered {w : W} (h : w∈init) : Ordered w := by
  change w∈raws++[seed] at h
  rcases List.mem_append.mp h with hr|hs
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    exact raw_order i
  · have e : w=seed := List.mem_singleton.mp hs
    rw [e]
    exact join_ordered true (raw_order 0) (raw_order 2)

theorem terminal_dist (S : Finset W) (finish : cleanCut model label 6 S) (i : Row) :
    ∃w∈S, cell w (lower i)≠cell w (upper i) := by
  have ne : label (lower i)≠label (upper i) := by rw [(labels i).1,(labels i).2]; decide
  exact finish.2.1 _ _ ne

theorem terminal_mark (S : Finset W) (finish : cleanCut model label 6 S) (i : Row) :
    ∃w∈S, bit (mark w).1 i≠bit (mark w).2 i := by
  obtain ⟨w,m,d⟩ := terminal_dist S finish i
  exact ⟨w,m,by rw [positive,negative]; exact Ne.symm d⟩

/-- These nine packed constants permit executing join homomorphically at the
numeric level without reprojecting 512-bit physical truth tables per state. -/
def basis : Fin 9 → Mark := ![(0x210fe00847f007e01f83e01107e03e042084423f0fc3c08220842122287e3e0f,0x7e00003f003e00f83e00003e01e000000001f0fc3c00000000000003e3e07),
  (0x3e0f82017c010fc20208423f0fc21e208410884411044517e1f805f05e7c20279,0x3e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038),
  (0x421043f883ff880041084422084244fc027c3e022ffc0f84010be21e40847fd0,0x1f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0),
  (0x84208421082110448ffc0044fffe00109f90089ff08802085ffc800897ffc480,0xffc0000fffe00001f80001ff00000001ffc000007ffc000),
  (0x3ff0101fffc400083f21081ff1084087fe4003fe441008fffe210001ff9088802,0x3ff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000),
  (0x10842084210822109042108882108917fffffc00802010fffffffffe000101004,0x7fffffc00000000fffffffffe000000000),
  (0x21084108421044213ffffff004001007ffffffffffffff0100400040102000020,0x3fffffe000000007ffffffffffffff0000000000000000000),
  (0x3ffffff0002080003ffffffffffffffa108211000041004208821085000002100,0x3fffffe0000000003ffffffffffffff8000000000000000000000000000000000),
  (0x3fffffffffffffffe084210008210004210422110882228411042108004210000,0x3fffffffffffffffc000000000000000000000000000000000000000000000000)]

theorem basis_matches : ∀ i : Fin 9, mark (raw i)=basis i := by
  intro i
  fin_cases i <;> decide +kernel

theorem seed_matches : mark seed=((basis 0).1 ||| (basis 2).1,(basis 0).2 ||| (basis 2).2) := by
  change mark (join true (raw 0) (raw 2))=_
  simp only [mark_gate,basis_matches,↓reduceIte]

#print axioms labels
#print axioms mark_gate
#print axioms terminal_mark
#print axioms basis_matches
end CoPortEdgeRows4482
