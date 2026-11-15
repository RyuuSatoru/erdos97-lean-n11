import A1_Checker_Closed_CANDIDATE
import A3_Checker_AllDirections_CANDIDATE
/-!
All positive rejection codes in the *finite checker* are geometrically sound,
conditional on a StrictCCW11 realization of both actual rows.
This does NOT prove that a U16 certificate covers every rejected table cell,
nor search completeness or the Erdős #97 end-to-end theorem.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97CheckReasonClosed
open E97AllowFinite E97CellSlot E97BlockB

/-- The Boolean checker rejects all out-of-range positive codes. -/
theorem checked_positive_code_le_4675
    (slot code : Nat) (hs : slot < 2425500)
    (hpos : 0 < code) (hcheck : checkReason slot code = true) :
    code ≤ 4675 := by
  by_contra hbound
  have hA1 : ¬ code ≤ 55 := by omega
  have hA3 : ¬ code ≤ 4675 := by omega
  have hnonzero : code ≠ 0 := Nat.ne_of_gt hpos
  unfold checkReason at hcheck
  simp only [ite_eq_left hs, ite_eq_right hnonzero,
             ite_eq_right hA1, ite_eq_right hA3] at hcheck
  cases hcheck

/-- Main next milestone: all positive accepted rejection codes exclude
any pair of actual row realizations in a strictly convex 11-vertex model. -/
theorem checkReason_positive_sound
    (P : Fin 11 → XY) (hccw : E97A1Index.StrictCCW11 P)
    (slot code : Nat) (hs : slot < 2425500) (hpos : 0 < code)
    (hA : E97AllowSound.SelectedRowRealization P
      (210 * centerA slot + rowX slot))
    (hB : E97AllowSound.SelectedRowRealization P
      (210 * centerB slot + rowY slot))
    (hcheck : checkReason slot code = true) : False := by
  by_cases hA1 : code ≤ 55
  · exact E97A1Closed.checked_A1_no_distinctness P hccw slot code
      hs hpos hA1 hA hB hcheck
  · have hlo : 55 < code := by omega
    have hhi : code ≤ 4675 :=
      checked_positive_code_le_4675 slot code hs hpos hcheck
    by_cases hBC : (code - 56) % 2 = 0
    · exact E97A3AllDirections.checked_BC_all_directions P hccw
        slot code hs hlo hhi hBC hA hB hcheck
    · exact E97A3AllDirections.checked_AB_all_directions P hccw
        slot code hs hlo hhi hBC hA hB hcheck

#print axioms E97CheckReasonClosed.checked_positive_code_le_4675
#print axioms E97CheckReasonClosed.checkReason_positive_sound
end E97CheckReasonClosed
