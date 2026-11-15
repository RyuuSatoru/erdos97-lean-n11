import BE_BitmaskArithmetic_CANDIDATE
import A2_SelectedPrefixCounts_CANDIDATE

/-!
The finite, actual getRow data uses the same eleven-vertex bitmask
interpretation as the C++ verifier. This checks EACH of the 2310 rows and
11 vertices. This is not yet an A3 no-goods generator or a tree verifier.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace E97Bitmask
open E97A2Rows E97Flow

def fourBits (a b c d : Nat) : Nat :=
  ((bit a ||| bit b) ||| bit c) ||| bit d

def actualRowMask (p : Nat) : Nat :=
  let (a,b,c,d) := decodedWitnesses p
  fourBits a b c d

/-- Check actual row mask against the four decoded witness vertices. -/
def actualRowMaskOK (p : Nat) : Bool :=
  let (a,b,c,d) := decodedWitnesses p
  decide (actualRowMask p < 2048) &&
  (List.range 11).all (fun u =>
    hasBit (actualRowMask p) u ==
    decide (u = a ∨ u = b ∨ u = c ∨ u = d))

/-- All 11 * 210 actual rows have the exact C++ witness bitmask. -/
theorem allActualRowMasksOK :
    (List.range 2310).all actualRowMaskOK = true := by decide

#print axioms E97Bitmask.allActualRowMasksOK
end E97Bitmask
