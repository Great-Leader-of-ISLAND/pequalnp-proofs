import PEqualNP.CoThetaSeed3024Data

namespace CoThetaSeed3024
open CoAO3143 CoAO3143.Memo
set_option maxRecDepth 16384
set_option maxHeartbeats 0
theorem v0 : Valid (table 0) 0 := by intro i h; exact (Nat.not_lt_zero _ h).elim
theorem v1 : Valid (table 1) 1 := by intro i h; exact (Nat.not_lt_zero _ h).elim
theorem v2 : Valid (table 2) 2 := by intro i h; exact (Nat.not_lt_zero _ h).elim
theorem v3 : Valid (table 3) 3 := by intro i h; exact (Nat.not_lt_zero _ h).elim
theorem v4 : Valid (table 4) 4 := by intro i h; exact (Nat.not_lt_zero _ h).elim
theorem v5 : Valid (table 5) 5 := by intro i h; exact (Nat.not_lt_zero _ h).elim
def test6 (i : Nat) := node (ProtocolProof.grid 7 8) 5 (table 5) ((table 6).state i)
theorem g6_0 (b : Fin 8) : allAt test6 ((0*8+b.val)*6) (min 6 (71-((0*8+b.val)*6)))=true := by fin_cases b <;> decide +kernel
theorem g6_1 (b : Fin 8) : allAt test6 ((1*8+b.val)*6) (min 6 (71-((1*8+b.val)*6)))=true := by fin_cases b <;> decide +kernel
theorem v6 : Valid (table 6) 6 := by
  apply grouped_layer (g := ProtocolProof.grid 7 8) v5 6 (by decide) 2 (by decide +kernel)
  intro a b
  fin_cases a
  · exact g6_0 b
  · exact g6_1 b
def test7 (i : Nat) := node (ProtocolProof.grid 7 8) 6 (table 6) ((table 7).state i)
theorem g7_0 (b : Fin 8) : allAt test7 ((0*8+b.val)*6) (min 6 (359-((0*8+b.val)*6)))=true := by fin_cases b <;> decide +kernel
theorem g7_1 (b : Fin 8) : allAt test7 ((1*8+b.val)*6) (min 6 (359-((1*8+b.val)*6)))=true := by fin_cases b <;> decide +kernel
theorem g7_2 (b : Fin 8) : allAt test7 ((2*8+b.val)*6) (min 6 (359-((2*8+b.val)*6)))=true := by fin_cases b <;> decide +kernel
theorem g7_3 (b : Fin 8) : allAt test7 ((3*8+b.val)*6) (min 6 (359-((3*8+b.val)*6)))=true := by fin_cases b <;> decide +kernel
theorem g7_4 (b : Fin 8) : allAt test7 ((4*8+b.val)*6) (min 6 (359-((4*8+b.val)*6)))=true := by fin_cases b <;> decide +kernel
theorem g7_5 (b : Fin 8) : allAt test7 ((5*8+b.val)*6) (min 6 (359-((5*8+b.val)*6)))=true := by fin_cases b <;> decide +kernel
theorem g7_6 (b : Fin 8) : allAt test7 ((6*8+b.val)*6) (min 6 (359-((6*8+b.val)*6)))=true := by fin_cases b <;> decide +kernel
theorem g7_7 (b : Fin 8) : allAt test7 ((7*8+b.val)*6) (min 6 (359-((7*8+b.val)*6)))=true := by fin_cases b <;> decide +kernel
theorem v7 : Valid (table 7) 7 := by
  apply grouped_layer (g := ProtocolProof.grid 7 8) v6 6 (by decide) 8 (by decide +kernel)
  intro a b
  fin_cases a
  · exact g7_0 b
  · exact g7_1 b
  · exact g7_2 b
  · exact g7_3 b
  · exact g7_4 b
  · exact g7_5 b
  · exact g7_6 b
  · exact g7_7 b
def test8 (i : Nat) := node (ProtocolProof.grid 7 8) 7 (table 7) ((table 8).state i)
theorem g8_0 (b : Fin 8) : allAt test8 ((0*8+b.val)*6) (min 6 (577-((0*8+b.val)*6)))=true := by fin_cases b <;> decide +kernel
theorem g8_1 (b : Fin 8) : allAt test8 ((1*8+b.val)*6) (min 6 (577-((1*8+b.val)*6)))=true := by fin_cases b <;> decide +kernel
theorem g8_2 (b : Fin 8) : allAt test8 ((2*8+b.val)*6) (min 6 (577-((2*8+b.val)*6)))=true := by fin_cases b <;> decide +kernel
theorem g8_3 (b : Fin 8) : allAt test8 ((3*8+b.val)*6) (min 6 (577-((3*8+b.val)*6)))=true := by fin_cases b <;> decide +kernel
theorem g8_4 (b : Fin 8) : allAt test8 ((4*8+b.val)*6) (min 6 (577-((4*8+b.val)*6)))=true := by fin_cases b <;> decide +kernel
theorem g8_5 (b : Fin 8) : allAt test8 ((5*8+b.val)*6) (min 6 (577-((5*8+b.val)*6)))=true := by fin_cases b <;> decide +kernel
theorem g8_6 (b : Fin 8) : allAt test8 ((6*8+b.val)*6) (min 6 (577-((6*8+b.val)*6)))=true := by fin_cases b <;> decide +kernel
theorem g8_7 (b : Fin 8) : allAt test8 ((7*8+b.val)*6) (min 6 (577-((7*8+b.val)*6)))=true := by fin_cases b <;> decide +kernel
theorem g8_8 (b : Fin 8) : allAt test8 ((8*8+b.val)*6) (min 6 (577-((8*8+b.val)*6)))=true := by fin_cases b <;> decide +kernel
theorem g8_9 (b : Fin 8) : allAt test8 ((9*8+b.val)*6) (min 6 (577-((9*8+b.val)*6)))=true := by fin_cases b <;> decide +kernel
theorem g8_10 (b : Fin 8) : allAt test8 ((10*8+b.val)*6) (min 6 (577-((10*8+b.val)*6)))=true := by fin_cases b <;> decide +kernel
theorem g8_11 (b : Fin 8) : allAt test8 ((11*8+b.val)*6) (min 6 (577-((11*8+b.val)*6)))=true := by fin_cases b <;> decide +kernel
theorem g8_12 (b : Fin 8) : allAt test8 ((12*8+b.val)*6) (min 6 (577-((12*8+b.val)*6)))=true := by fin_cases b <;> decide +kernel
theorem v8 : Valid (table 8) 8 := by
  apply grouped_layer (g := ProtocolProof.grid 7 8) v7 6 (by decide) 13 (by decide +kernel)
  intro a b
  fin_cases a
  · exact g8_0 b
  · exact g8_1 b
  · exact g8_2 b
  · exact g8_3 b
  · exact g8_4 b
  · exact g8_5 b
  · exact g8_6 b
  · exact g8_7 b
  · exact g8_8 b
  · exact g8_9 b
  · exact g8_10 b
  · exact g8_11 b
  · exact g8_12 b
def test9 (i : Nat) := node (ProtocolProof.grid 7 8) 8 (table 8) ((table 9).state i)
theorem g9_0 (b : Fin 8) : allAt test9 ((0*8+b.val)*6) (min 6 (113-((0*8+b.val)*6)))=true := by fin_cases b <;> decide +kernel
theorem g9_1 (b : Fin 8) : allAt test9 ((1*8+b.val)*6) (min 6 (113-((1*8+b.val)*6)))=true := by fin_cases b <;> decide +kernel
theorem g9_2 (b : Fin 8) : allAt test9 ((2*8+b.val)*6) (min 6 (113-((2*8+b.val)*6)))=true := by fin_cases b <;> decide +kernel
theorem v9 : Valid (table 9) 9 := by
  apply grouped_layer (g := ProtocolProof.grid 7 8) v8 6 (by decide) 3 (by decide +kernel)
  intro a b
  fin_cases a
  · exact g9_0 b
  · exact g9_1 b
  · exact g9_2 b
def test10 (i : Nat) := node (ProtocolProof.grid 7 8) 9 (table 9) ((table 10).state i)
theorem g10_0 (b : Fin 8) : allAt test10 ((0*8+b.val)*6) (min 6 (3-((0*8+b.val)*6)))=true := by fin_cases b <;> decide +kernel
theorem v10 : Valid (table 10) 10 := by
  apply grouped_layer (g := ProtocolProof.grid 7 8) v9 6 (by decide) 1 (by decide +kernel)
  intro a b
  fin_cases a
  · exact g10_0 b
def plain : List Sig := [(0x3f8001fc07f0003f8001fc07f0003f8001fc07f,0x850a142850a142850a142850a142850a142850a1),(0xfc000fe03f8001fc000fe03f8001fc000fe03f80,0xc183060c183060c183060c183060c183060c183),(0x3fff00000000003fff00000000003fff,0x72e5cb972e5cb972e5cb972e5cb972e5cb972e5c),(0x7f01fc000000007f01fc000000007f01fc000,0x58b162c58b162c58b162c58b162c58b162c58b16),(0x7ffe00000000007ffe00000000007ffe00000,0xa3468d1a3468d1a3468d1a3468d1a3468d1a3468),(0x3f800000000fe03f800000000fe03f800000000,0x3870e1c3870e1c3870e1c3870e1c3870e1c3870e),(0xfc0000000000fffc0000000000fffc0000000000,0xc3870e1c3870e1c3870e1c3870e1c3870e1c3870)]
theorem plain_impossible : Impossible 10 0 plain := by
  have v := v10 2 (by decide +kernel)
  have eq : ((table 10).state 2).toFinset=plain.toFinset := by decide +kernel
  simpa only [Impossible,eq] using v
def seeded : List Sig := [(0x3f8001fc07f0003f8001fc07f0003f8001fc07f,0x850a142850a142850a142850a142850a142850a1),(0xfc000fe03f8001fc000fe03f8001fc000fe03f80,0xc183060c183060c183060c183060c183060c183),(0x3fff00000000003fff00000000003fff,0x72e5cb972e5cb972e5cb972e5cb972e5cb972e5c),(0x7f01fc000000007f01fc000000007f01fc000,0x58b162c58b162c58b162c58b162c58b162c58b16),(0x7ffe00000000007ffe00000000007ffe00000,0xa3468d1a3468d1a3468d1a3468d1a3468d1a3468),(0x3f800000000fe03f800000000fe03f800000000,0x3870e1c3870e1c3870e1c3870e1c3870e1c3870e),(0xfc0000000000fffc0000000000fffc0000000000,0xc3870e1c3870e1c3870e1c3870e1c3870e1c3870),(0xfc07f01fc000fffc07f01fc000fffc07f01fc000,0xdbb76eddbb76eddbb76eddbb76eddbb76eddbb76)]
theorem seeded_impossible : Impossible 10 0 seeded := by
  have v := v10 1 (by decide +kernel)
  have eq : ((table 10).state 1).toFinset=seeded.toFinset := by decide +kernel
  simpa only [Impossible,eq] using v
end CoThetaSeed3024
