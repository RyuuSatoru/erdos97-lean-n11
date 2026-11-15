import RowMask_Bridge_Core_CANDIDATE
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97RowMaskC10
/-- All 210 witness masks for center 10, checked by Lean kernel reduction. -/
theorem check : E97RowBridge.centerScan 10 = true := by decide +kernel
#print axioms E97RowMaskC10.check
end E97RowMaskC10
