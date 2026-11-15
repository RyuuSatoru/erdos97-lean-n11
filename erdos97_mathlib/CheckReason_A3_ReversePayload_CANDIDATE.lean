import CheckReason_A3_CenterRoute_CANDIDATE
/-!
The reversed branch of checkReason A3 supplies the BC/AB bitmasks on
oppositely ordered cell centers. No geometric claim is made here.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97A3ReversePayload
open E97AllowFinite E97CellSlot

/-- A reversed A3 pattern forces the two masks, swapped across the actual rows. -/
theorem checked_reverse_masks (slot code : Nat)
    (hs : slot < 2425500) (hlo : 55 < code) (hhi : code ≤ 4675)
    (hcheck : checkReason slot code = true)
    (hreverse : (patternAt (code - 56)).c = centerB slot ∧
                (patternAt (code - 56)).d = centerA slot) :
    containsBits (rowMask (centerB slot) (rowY slot))
      (patternAt (code - 56)).mc = true ∧
    containsBits (rowMask (centerA slot) (rowX slot))
      (patternAt (code - 56)).md = true := by
  have hp := E97ReasonPayload.a3_payload slot code hs hlo hhi hcheck
  rw [cellData_exact] at hp
  change (if (patternAt (code - 56)).c = centerA slot ∧
              (patternAt (code - 56)).d = centerB slot then
            containsBits (rowMask (centerA slot) (rowX slot))
              (patternAt (code - 56)).mc &&
            containsBits (rowMask (centerB slot) (rowY slot))
              (patternAt (code - 56)).md
          else if (patternAt (code - 56)).c = centerB slot ∧
                  (patternAt (code - 56)).d = centerA slot then
            containsBits (rowMask (centerB slot) (rowY slot))
              (patternAt (code - 56)).mc &&
            containsBits (rowMask (centerA slot) (rowX slot))
              (patternAt (code - 56)).md
          else false) = true at hp
  have hnot : ¬ ((patternAt (code - 56)).c = centerA slot ∧
                 (patternAt (code - 56)).d = centerB slot) := by
    intro hf
    have hab : centerA slot < centerB slot := (slot_bounds slot hs).1
    have heq : centerA slot = centerB slot := hf.1.symm.trans hreverse.1
    omega
  -- First eliminate the forward guard while its original syntax is intact.
  simp [hnot] at hp
  -- Only then rewrite the reversed center equations.
  simpa [hreverse, Bool.and_eq_true] using hp

#print axioms E97A3ReversePayload.checked_reverse_masks
end E97A3ReversePayload
