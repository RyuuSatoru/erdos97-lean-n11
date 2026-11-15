import Mask_Intersection_Checker_V33
import Intersection_Certificate_Quote_V33
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace T34Root027
def b00082 : T33Checker.Certificate := e97IntersectionCertificate "/persistent/root_tokens_v33/Root_027_V33.tokens" at 2603526
theorem b00082_ok : T33Checker.checkTree 11 T33Checker.suggestedHints [27,406] b00082 = true := by decide +kernel

#print axioms T34Root027.b00082_ok
#print axioms T34Root027.b00082
end T34Root027
