import Mask_Intersection_Checker_V33
import Intersection_Certificate_Quote_V33
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace T34Root195
def b00000 : T33Checker.Certificate := e97IntersectionCertificate "/persistent/root_tokens_v33/Root_195_V33.tokens" at 0
theorem b00000_ok : T33Checker.checkTree 12 T33Checker.suggestedHints [195] b00000 = true := by decide +kernel
abbrev certificate := b00000
theorem accepted : T33Checker.checkTree 12 T33Checker.suggestedHints [195] certificate = true := b00000_ok
#print axioms T34Root195.accepted
#print axioms T34Root195.certificate
end T34Root195
