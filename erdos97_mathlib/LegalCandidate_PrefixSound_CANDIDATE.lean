import Allow_Certificate_Interface_CANDIDATE
/-!
The pairwise-Allow component of the B/E search domain. The candidate
must be compatible with every previously chosen row, irrespective of which
of the two centers comes first in the certificate's ordered slot.
This is NOT yet the whole search legalCandidate: the A2 budget, row
selection/exhaustiveness, and tree replay remain separate obligations.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace E97LegalPrefix
open E97CertBridge E97CellSlot E97BlockB

/-- All previously chosen actual rows can be realized in the same geometry. -/
def RealizablePrefix (P : Fin 11 → XY) (chosenRows : List Nat) : Prop :=
  ∀ r, r ∈ chosenRows → E97AllowSound.SelectedRowRealization P r

/-- Pairwise-Allow eligibility in both orientations for a new actual row. -/
def PairwiseLegalCandidate
    (reasonAt : Nat → Nat) (chosenRows : List Nat) (nextRow : Nat) : Prop :=
  ∀ slot, slot < 2425500 →
    (((210 * centerA slot + rowX slot) ∈ chosenRows ∧
        nextRow = 210 * centerB slot + rowY slot) ∨
     ((210 * centerB slot + rowY slot) ∈ chosenRows ∧
        nextRow = 210 * centerA slot + rowX slot)) →
    AllowedSlot reasonAt slot

/-- If the U16 reasons are correct, pairwise-Allow never excludes an
actual row compatible with a realizable chosenRows, including reversed centers. -/
theorem realized_candidate_survives_pairwise_allow
    (reasonAt : Nat → Nat) (hcert : CertifiedReasonTable reasonAt)
    (P : Fin 11 → XY) (hccw : E97A1Index.StrictCCW11 P)
    (chosenRows : List Nat) (nextRow : Nat)
    (hprefix : RealizablePrefix P chosenRows)
    (hnext : E97AllowSound.SelectedRowRealization P nextRow) :
    PairwiseLegalCandidate reasonAt chosenRows nextRow := by
  intro slot hs hor
  rcases hor with ⟨hmem, heq⟩ | ⟨hmem, heq⟩
  · have hA := hprefix _ hmem
    have hB : E97AllowSound.SelectedRowRealization P
        (210 * centerB slot + rowY slot) := by
      simpa only [heq] using hnext
    exact realized_slot_allowed reasonAt hcert P hccw slot hs hA hB
  · have hB := hprefix _ hmem
    have hA : E97AllowSound.SelectedRowRealization P
        (210 * centerA slot + rowX slot) := by
      simpa only [heq] using hnext
    exact realized_slot_allowed reasonAt hcert P hccw slot hs hA hB

#print axioms E97LegalPrefix.realized_candidate_survives_pairwise_allow
end E97LegalPrefix
