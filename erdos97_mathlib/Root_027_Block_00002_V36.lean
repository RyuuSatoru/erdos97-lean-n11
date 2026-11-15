import Mask_Intersection_Checker_V33
import Intersection_Certificate_Quote_V33
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace T34Root027
def b00002 : T33Checker.Certificate := e97IntersectionCertificate "/persistent/root_tokens_v33/Root_027_V33.tokens" at 60167
theorem b00002_ok : T33Checker.checkTree 11 T33Checker.suggestedHints [27,240] b00002 = true := by decide +kernel

#print axioms T34Root027.b00002_ok
#print axioms T34Root027.b00002
end T34Root027
