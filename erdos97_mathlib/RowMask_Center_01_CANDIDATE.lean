import RowMask_Bridge_Core_CANDIDATE
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97RowMaskC01
/-- All 210 witness masks for center 1, checked by Lean kernel reduction. -/
theorem check : E97RowBridge.centerScan 1 = true := by decide +kernel
#print axioms E97RowMaskC01.check
end E97RowMaskC01
