import Mask_Intersection_Checker_V33
import Intersection_Certificate_Quote_V33
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace T34Root027
def b00046 : T33Checker.Certificate := e97IntersectionCertificate "/persistent/root_tokens_v33/Root_027_V33.tokens" at 1296253
theorem b00046_ok : T33Checker.checkTree 11 T33Checker.suggestedHints [27,361] b00046 = true := by decide +kernel

#print axioms T34Root027.b00046_ok
#print axioms T34Root027.b00046
end T34Root027
