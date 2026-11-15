import AllowFiniteReasonCore_CANDIDATE
/-!
E97 checkReason -> geometry, step 1:
Kernel-check the structural precondition that the 55 coded unordered pairs
are actually increasing vertex indices in 0..10. Does not inspect Allow U16.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97CheckReason
open E97AllowFinite

def validPairAt (i : Nat) : Bool :=
  let (a, b) := pairAt i
  decide (a < b ∧ b < 11)

/-- All 55 decoded vertex pairs have legal, distinct indices. -/
theorem all_pair_indices_wellformed :
    (List.range 55).all validPairAt = true := by decide

/-- The verified finite scan provides usable bounds for any table pair. -/
theorem pair_indices_wellformed (i : Nat) (hi : i < 55) :
    (pairAt i).1 < (pairAt i).2 ∧ (pairAt i).2 < 11 := by
  have h := (List.all_eq_true.mp all_pair_indices_wellformed) i
    (List.mem_range.mpr hi)
  rcases hpair : pairAt i with ⟨a, b⟩
  have hab : a < b ∧ b < 11 := by
    simpa [validPairAt, hpair] using h
  simpa [hpair] using hab

#print axioms E97CheckReason.all_pair_indices_wellformed
#print axioms E97CheckReason.pair_indices_wellformed
end E97CheckReason
