import CellData_Slot_Decode_CANDIDATE
import ReasonPayload_CANDIDATE
/-!
A positive checked A3 reason forces its pattern to address exactly the two
cell centers, in one of the two possible orders.  Does NOT claim geometry
soundness for the reversed order; that is a separate open obligation.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97CenterRoute
open E97AllowFinite E97CellSlot

/-- A3 true cannot arise from an unrelated pair of centers. -/
theorem checked_a3_routes (slot code : Nat)
    (hs : slot < 2425500) (hlo : 55 < code) (hhi : code ≤ 4675)
    (hcheck : checkReason slot code = true) :
    ((patternAt (code - 56)).c = centerA slot ∧
     (patternAt (code - 56)).d = centerB slot) ∨
    ((patternAt (code - 56)).c = centerB slot ∧
     (patternAt (code - 56)).d = centerA slot) := by
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
  by_cases hf : (patternAt (code - 56)).c = centerA slot ∧
                (patternAt (code - 56)).d = centerB slot
  · exact Or.inl hf
  · by_cases hr : (patternAt (code - 56)).c = centerB slot ∧
                  (patternAt (code - 56)).d = centerA slot
    · exact Or.inr hr
    · simp [hf, hr] at hp

/-- In particular the pattern centers are either increasing or decreasing. -/
theorem checked_a3_order (slot code : Nat)
    (hs : slot < 2425500) (hlo : 55 < code) (hhi : code ≤ 4675)
    (hcheck : checkReason slot code = true) :
    (patternAt (code - 56)).c < (patternAt (code - 56)).d ∨
    (patternAt (code - 56)).d < (patternAt (code - 56)).c := by
  have hb := (slot_bounds slot hs).1
  rcases checked_a3_routes slot code hs hlo hhi hcheck with hf | hr
  · left
    rcases hf with ⟨hc, hd⟩
    rw [hc, hd]
    exact hb
  · right
    rcases hr with ⟨hc, hd⟩
    rw [hd, hc]
    exact hb

#print axioms E97CenterRoute.checked_a3_routes
#print axioms E97CenterRoute.checked_a3_order
end E97CenterRoute
