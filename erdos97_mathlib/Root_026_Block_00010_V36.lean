import Mask_Intersection_Checker_V33
import Intersection_Certificate_Quote_V33
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace T34Root026
def b00010 : T33Checker.Certificate := e97IntersectionCertificate "/persistent/root_tokens_v33/Root_026_V33.tokens" at 417156
theorem b00010_ok : T33Checker.checkTree 11 T33Checker.suggestedHints [26,250] b00010 = true := by decide +kernel

#print axioms T34Root026.b00010_ok
#print axioms T34Root026.b00010
end T34Root026
