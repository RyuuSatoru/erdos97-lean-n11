import CheckReason_AllPositive_Sound_CANDIDATE
/-!
A proof interface for an arbitrary U16-like table. The table's actual bytes
must STILL be tied to this function by a separate kernel-verified computation.
This module does not claim to verify any table entries.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97CertBridge
open E97AllowFinite E97CellSlot E97BlockB

/-- The *remaining* pointwise certificate condition: every nonzero entry
names a positive A1/A3 reason accepted by the finite checker. -/
def CertifiedReasonTable (reasonAt : Nat → Nat) : Prop :=
  ∀ slot, slot < 2425500 → reasonAt slot ≠ 0 →
    checkReason slot (reasonAt slot) = true

/-- A table entry is allowed precisely when its reason code is zero. -/
def AllowedSlot (reasonAt : Nat → Nat) (slot : Nat) : Prop :=
  reasonAt slot = 0

/-- Positive-code geometric soundness now implies the *conservative* Allow
 property for any table satisfying the separate certificate condition. -/
theorem realized_slot_allowed
    (reasonAt : Nat → Nat) (hcert : CertifiedReasonTable reasonAt)
    (P : Fin 11 → XY) (hccw : E97A1Index.StrictCCW11 P)
    (slot : Nat) (hs : slot < 2425500)
    (hA : E97AllowSound.SelectedRowRealization P
      (210 * centerA slot + rowX slot))
    (hB : E97AllowSound.SelectedRowRealization P
      (210 * centerB slot + rowY slot)) :
    AllowedSlot reasonAt slot := by
  by_contra hn
  have hnz : reasonAt slot ≠ 0 := by
    simpa only [AllowedSlot] using hn
  have hp : 0 < reasonAt slot := by omega
  exact E97CheckReasonClosed.checkReason_positive_sound
    P hccw slot (reasonAt slot) hs hp hA hB (hcert slot hs hnz)

#print axioms E97CertBridge.realized_slot_allowed
end E97CertBridge
