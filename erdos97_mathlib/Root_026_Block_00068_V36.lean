import Mask_Intersection_Checker_V33
import Intersection_Certificate_Quote_V33
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace T34Root026
def b00068 : T33Checker.Certificate := e97IntersectionCertificate "/persistent/root_tokens_v33/Root_026_V33.tokens" at 1990561
theorem b00068_ok : T33Checker.checkTree 11 T33Checker.suggestedHints [26,403] b00068 = true := by decide +kernel

#print axioms T34Root026.b00068_ok
#print axioms T34Root026.b00068
end T34Root026
