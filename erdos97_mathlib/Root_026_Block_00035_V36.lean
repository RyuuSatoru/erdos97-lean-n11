import Mask_Intersection_Checker_V33
import Intersection_Certificate_Quote_V33
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace T34Root026
def b00035 : T33Checker.Certificate := e97IntersectionCertificate "/persistent/root_tokens_v33/Root_026_V33.tokens" at 1140096
theorem b00035_ok : T33Checker.checkTree 11 T33Checker.suggestedHints [26,355] b00035 = true := by decide +kernel

#print axioms T34Root026.b00035_ok
#print axioms T34Root026.b00035
end T34Root026
