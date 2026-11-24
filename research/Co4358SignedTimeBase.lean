import PEqualNP.Co4358SignedTiming

namespace Co4358Timing
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sampleBase : originalSearch LO LO 9 kv17 511 491 322 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f = false := by decide +kernel
end Co4358Timing
