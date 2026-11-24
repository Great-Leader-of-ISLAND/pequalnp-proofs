import PEqualNP.Co4358BitsBench
namespace CoNum4358.Tiny.CanonicalSample
open CoNum4358.Tiny.QuickBench (test)
set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 20
def rows3 : List Nat := [11]
theorem level3 : rows3.all (test 2)=true := by decide +kernel
def rows4 : List Nat := [13, 53]
theorem level4 : rows4.all (test 3)=true := by decide +kernel
def rows5 : List Nat := [12, 55, 97, 152]
theorem level5 : rows5.all (test 4)=true := by decide +kernel
def rows6 : List Nat := [20, 56, 99, 170, 196, 236, 284, 388]
theorem level6 : rows6.all (test 5)=true := by decide +kernel
def rows7 : List Nat := [11, 55, 81, 105, 130, 173, 228, 330, 354, 384, 408, 434, 487, 628]
theorem level7 : rows7.all (test 6)=true := by decide +kernel
def rows8 : List Nat := [12, 36, 80, 162, 188, 212, 244, 273, 298, 329, 374, 474, 601, 636, 662, 690]
theorem level8 : rows8.all (test 7)=true := by decide +kernel
def rows9 : List Nat := [10, 54, 97, 124, 149, 176, 225, 291, 311, 345, 414, 445]
theorem level9 : rows9.all (test 8)=true := by decide +kernel
def rows10 : List Nat := [2, 9, 17, 22, 30, 36]
theorem level10 : rows10.all (test 9)=true := by decide +kernel
def rows11 : List Nat := [0]
theorem level11 : rows11.all (test 10)=true := by decide +kernel
end CoNum4358.Tiny.CanonicalSample
