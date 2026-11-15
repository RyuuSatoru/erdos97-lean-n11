import RowMask_Bridge_Core_CANDIDATE
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97RowMaskC04
/-- All 210 witness masks for center 4, checked by Lean kernel reduction. -/
theorem check : E97RowBridge.centerScan 4 = true := by decide +kernel
#print axioms E97RowMaskC04.check
end E97RowMaskC04
