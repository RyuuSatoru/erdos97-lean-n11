import CheckReason_A3_CenterRoute_CANDIDATE
import A3_PatternAt_Geometry_Transport_CANDIDATE
/-!
Removes manually supplied hcell for the forward BC/AB orientation, using
the kernel-checked cellData decoder and slot bounds.  Pattern centers in
reverse order still need their own transport and are NOT addressed here.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97A3CellForward
open E97AllowFinite E97CellSlot E97A3Pattern E97BlockB E97AllowSound

/-- A3 BC: no extra equality assumption on cellData is needed. -/
theorem checked_BC_forward (P : Fin 11 → XY)
    (hccw : E97A1Index.StrictCCW11 P)
    (slot code : Nat) (hs : slot < 2425500)
    (hlo : 55 < code) (hhi : code ≤ 4675)
    (heven : (code - 56) % 2 = 0)
    (hforward : centerA slot = vertex code 2 ∧ centerB slot = vertex code 3)
    (hA : SelectedRowRealization P (210 * centerA slot + rowX slot))
    (hB : SelectedRowRealization P (210 * centerB slot + rowY slot))
    (hcheck : checkReason slot code = true) : False := by
  rcases hforward with ⟨ha, hb⟩
  have hcell : cellData slot =
      (vertex code 2, vertex code 3, rowX slot, rowY slot,
       rowMask (vertex code 2) (rowX slot),
       rowMask (vertex code 3) (rowY slot)) := by
    simpa only [ha, hb] using cellData_exact slot
  have hx : rowX slot < 210 := (slot_bounds slot hs).2.2.1
  have hy : rowY slot < 210 := (slot_bounds slot hs).2.2.2
  have hA' : SelectedRowRealization P (210 * vertex code 2 + rowX slot) := by
    simpa only [ha] using hA
  have hB' : SelectedRowRealization P (210 * vertex code 3 + rowY slot) := by
    simpa only [hb] using hB
  exact A3_BC_checked_geometry_from_code P hccw slot code
    (rowX slot) (rowY slot) hs hlo hhi heven hcell hx hy hA' hB' hcheck

/-- A3 AB: same structural bridge for the reflected branch. -/
theorem checked_AB_forward (P : Fin 11 → XY)
    (hccw : E97A1Index.StrictCCW11 P)
    (slot code : Nat) (hs : slot < 2425500)
    (hlo : 55 < code) (hhi : code ≤ 4675)
    (hodd : (code - 56) % 2 ≠ 0)
    (hforward : centerA slot = vertex code 1 ∧ centerB slot = vertex code 2)
    (hA : SelectedRowRealization P (210 * centerA slot + rowX slot))
    (hB : SelectedRowRealization P (210 * centerB slot + rowY slot))
    (hcheck : checkReason slot code = true) : False := by
  rcases hforward with ⟨ha, hb⟩
  have hcell : cellData slot =
      (vertex code 1, vertex code 2, rowX slot, rowY slot,
       rowMask (vertex code 1) (rowX slot),
       rowMask (vertex code 2) (rowY slot)) := by
    simpa only [ha, hb] using cellData_exact slot
  have hx : rowX slot < 210 := (slot_bounds slot hs).2.2.1
  have hy : rowY slot < 210 := (slot_bounds slot hs).2.2.2
  have hA' : SelectedRowRealization P (210 * vertex code 1 + rowX slot) := by
    simpa only [ha] using hA
  have hB' : SelectedRowRealization P (210 * vertex code 2 + rowY slot) := by
    simpa only [hb] using hB
  exact A3_AB_checked_geometry_from_code P hccw slot code
    (rowX slot) (rowY slot) hs hlo hhi hodd hcell hx hy hA' hB' hcheck

#print axioms E97A3CellForward.checked_BC_forward
#print axioms E97A3CellForward.checked_AB_forward
end E97A3CellForward
