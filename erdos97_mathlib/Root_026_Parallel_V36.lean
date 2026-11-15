import Mask_Intersection_Checker_V33
import Intersection_Certificate_Quote_V33
import Root_026_Block_00075_V36
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace T34Root026
abbrev certificate := b00075
theorem accepted : T33Checker.checkTree 12 T33Checker.suggestedHints [26] certificate = true := b00075_ok
#print axioms T34Root026.accepted
#print axioms T34Root026.certificate
end T34Root026
