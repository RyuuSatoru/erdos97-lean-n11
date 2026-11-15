import Mask_Intersection_Checker_V33
import Intersection_Certificate_Quote_V33
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace T34Root026
def b00051 : T33Checker.Certificate := e97IntersectionCertificate "/persistent/root_tokens_v33/Root_026_V33.tokens" at 1510054
theorem b00051_ok : T33Checker.checkTree 11 T33Checker.suggestedHints [26,375] b00051 = true := by decide +kernel

#print axioms T34Root026.b00051_ok
#print axioms T34Root026.b00051
end T34Root026
