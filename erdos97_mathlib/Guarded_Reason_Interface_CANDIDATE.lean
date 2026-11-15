import LegalCandidate_PrefixSound_CANDIDATE
/-!
E97: UNTRUSTED-INPUT, CHECK-ON-USE certificate strategy.
The U16 bytes are merely hints. Any nonzero reason is used ONLY if
checkReason validates it. A rejected/invalid hint becomes code zero (ALLOW),
so malformed input cannot unsoundly exclude an actual geometric pair.
This module needs NO complete U16 scan or 2100 proof shards.
The eventual tree verifier MUST consume guardedReasonAt, never the raw table.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97Guarded
open E97AllowFinite E97CertBridge

/-- Validate the untrusted supplied reason each time it is consulted.
    If validation fails, refuse to exclude the corresponding pair. -/
def guardedReasonAt (rawReasonAt : Nat → Nat) (slot : Nat) : Nat :=
  if checkReason slot (rawReasonAt slot) = true then
    rawReasonAt slot
  else 0

/-- Successful hints retain their value. -/
theorem guarded_eq_raw_of_valid
    (rawReasonAt : Nat → Nat) (slot : Nat)
    (h : checkReason slot (rawReasonAt slot) = true) :
    guardedReasonAt rawReasonAt slot = rawReasonAt slot := by
  simp [guardedReasonAt, h]

/-- Invalid hints are treated as allowed, rather than rejected. -/
theorem guarded_eq_zero_of_invalid
    (rawReasonAt : Nat → Nat) (slot : Nat)
    (h : ¬ checkReason slot (rawReasonAt slot) = true) :
    guardedReasonAt rawReasonAt slot = 0 := by
  simp [guardedReasonAt, h]

/-- CRITICAL: for EVERY raw source, without reading/validating its entire
    contents up front, the guarded table satisfies the existing global
    CertifiedReasonTable interface. No data-integrity hypothesis is needed. -/
theorem guarded_certificate (rawReasonAt : Nat → Nat) :
    CertifiedReasonTable (guardedReasonAt rawReasonAt) := by
  intro slot _hs hnz
  by_cases h : checkReason slot (rawReasonAt slot) = true
  · have heq := guarded_eq_raw_of_valid rawReasonAt slot h
    rw [heq]
    exact h
  · have hz := guarded_eq_zero_of_invalid rawReasonAt slot h
    exact False.elim (hnz hz)

/-- Soundness against an actual convex realization; no upfront U16 scan. -/
theorem realized_guarded_slot_allowed
    (rawReasonAt : Nat → Nat)
    (P : Fin 11 → E97BlockB.XY) (hccw : E97A1Index.StrictCCW11 P)
    (slot : Nat) (hs : slot < 2425500)
    (hA : E97AllowSound.SelectedRowRealization P
      (210 * E97CellSlot.centerA slot + E97CellSlot.rowX slot))
    (hB : E97AllowSound.SelectedRowRealization P
      (210 * E97CellSlot.centerB slot + E97CellSlot.rowY slot)) :
    AllowedSlot (guardedReasonAt rawReasonAt) slot := by
  exact E97CertBridge.realized_slot_allowed
    (guardedReasonAt rawReasonAt) (guarded_certificate rawReasonAt)
    P hccw slot hs hA hB

#print axioms E97Guarded.guarded_eq_raw_of_valid
#print axioms E97Guarded.guarded_eq_zero_of_invalid
#print axioms E97Guarded.guarded_certificate
#print axioms E97Guarded.realized_guarded_slot_allowed
end E97Guarded
