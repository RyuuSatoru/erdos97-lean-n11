import AllowFiniteReasonCore_CANDIDATE
import BE_ActualRowBitmask_CANDIDATE
/-! The two independently authored 11-vertex row encodings. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97RowBridge
open E97AllowFinite E97Bitmask
/-- Tests *actual* row bitmask, not an arbitrary fabricated mask. -/
def centerScan (c : Nat) : Bool :=
  (List.range 210).all (fun k => decide (rowMask c k = actualRowMask (210 * c + k)))
end E97RowBridge
