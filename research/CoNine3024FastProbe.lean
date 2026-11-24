import PEqualNP.CoNine3024Fast
import PEqualNP.CoNine3024Probe
namespace CoNine3024
set_option maxRecDepth 16384
set_option maxHeartbeats 0
example : (traceAt (geom 9) 13 (root 9 true) [0,0,0]).any (fun s => !(Fast.walk (geom 9) 10 s))=true := by decide +kernel
end CoNine3024
