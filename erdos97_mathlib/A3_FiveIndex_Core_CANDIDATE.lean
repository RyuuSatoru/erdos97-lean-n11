import AllowFiniteReasonCore_CANDIDATE
/-! Kernel-checkable 5-subset ordering used for all 462 A3 5-subsets.
    This file does NOT assert geometry or full certificate soundness. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97A3Index
open E97AllowFinite

def fiveIndex (i j : Nat) : Nat :=
  ((chooseK 5 (List.range 11)).getD i []).getD j 11

def validFiveIndex (i : Nat) : Bool :=
  decide (fiveIndex i 0 < fiveIndex i 1 ∧
          fiveIndex i 1 < fiveIndex i 2 ∧
          fiveIndex i 2 < fiveIndex i 3 ∧
          fiveIndex i 3 < fiveIndex i 4 ∧
          fiveIndex i 4 < 11)
end E97A3Index
