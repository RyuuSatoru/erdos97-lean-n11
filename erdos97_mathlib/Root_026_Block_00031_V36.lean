import Mask_Intersection_Checker_V33
import Intersection_Certificate_Quote_V33
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace T34Root026
def b00031 : T33Checker.Certificate := e97IntersectionCertificate "/persistent/root_tokens_v33/Root_026_V33.tokens" at 1049054
theorem b00031_ok : T33Checker.checkTree 11 T33Checker.suggestedHints [26,351] b00031 = true := by decide +kernel

#print axioms T34Root026.b00031_ok
#print axioms T34Root026.b00031
end T34Root026
