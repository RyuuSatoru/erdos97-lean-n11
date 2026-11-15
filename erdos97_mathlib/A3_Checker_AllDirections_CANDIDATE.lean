import A3_CellData_ReverseTransport_CANDIDATE
/-!
Complete A3 checker geometric transport for BOTH orientations of the centers.
Still conditional on real row realizations and StrictCCW11; does not establish
allow-table coverage, A1 distinctness, search completeness, or end-to-end proof.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97A3AllDirections
open E97AllowFinite E97CellSlot E97A3Pattern E97A3CellForward E97A3CellReverse
open E97BlockB E97AllowSound E97CenterRoute

/-- BC code: automatically dispatch forward versus reverse center routing. -/
theorem checked_BC_all_directions (P : Fin 11 → XY)
    (hccw : E97A1Index.StrictCCW11 P)
    (slot code : Nat) (hs : slot < 2425500)
    (hlo : 55 < code) (hhi : code ≤ 4675)
    (heven : (code - 56) % 2 = 0)
    (hA : SelectedRowRealization P (210 * centerA slot + rowX slot))
    (hB : SelectedRowRealization P (210 * centerB slot + rowY slot))
    (hcheck : checkReason slot code = true) : False := by
  have hpattern : patternAt (code - 56) =
      ⟨vertex code 2, vertex code 3,
       E97Bitmask.twoBits (vertex code 0) (vertex code 1),
       E97Bitmask.threeBits (vertex code 4) (vertex code 1) (vertex code 2)⟩ := by
    simpa only [vertex] using patternAt_bc (code - 56) heven
  rcases checked_a3_routes slot code hs hlo hhi hcheck with hf | hr
  · have hforward : centerA slot = vertex code 2 ∧
                     centerB slot = vertex code 3 := by
      constructor
      · calc
          centerA slot = (patternAt (code - 56)).c := hf.1.symm
          _ = vertex code 2 := by simp [hpattern]
      · calc
          centerB slot = (patternAt (code - 56)).d := hf.2.symm
          _ = vertex code 3 := by simp [hpattern]
    exact checked_BC_forward P hccw slot code hs hlo hhi heven
      hforward hA hB hcheck
  · have hreverse : centerA slot = vertex code 3 ∧
                     centerB slot = vertex code 2 := by
      constructor
      · calc
          centerA slot = (patternAt (code - 56)).d := hr.2.symm
          _ = vertex code 3 := by simp [hpattern]
      · calc
          centerB slot = (patternAt (code - 56)).c := hr.1.symm
          _ = vertex code 2 := by simp [hpattern]
    exact checked_BC_reverse P hccw slot code hs hlo hhi heven
      hreverse hA hB hcheck

/-- AB code: automatically dispatch forward versus reverse center routing. -/
theorem checked_AB_all_directions (P : Fin 11 → XY)
    (hccw : E97A1Index.StrictCCW11 P)
    (slot code : Nat) (hs : slot < 2425500)
    (hlo : 55 < code) (hhi : code ≤ 4675)
    (hodd : (code - 56) % 2 ≠ 0)
    (hA : SelectedRowRealization P (210 * centerA slot + rowX slot))
    (hB : SelectedRowRealization P (210 * centerB slot + rowY slot))
    (hcheck : checkReason slot code = true) : False := by
  have hpattern : patternAt (code - 56) =
      ⟨vertex code 1, vertex code 2,
       E97Bitmask.threeBits (vertex code 0) (vertex code 2) (vertex code 3),
       E97Bitmask.twoBits (vertex code 4) (vertex code 3)⟩ := by
    simpa only [vertex] using patternAt_ab (code - 56) hodd
  rcases checked_a3_routes slot code hs hlo hhi hcheck with hf | hr
  · have hforward : centerA slot = vertex code 1 ∧
                     centerB slot = vertex code 2 := by
      constructor
      · calc
          centerA slot = (patternAt (code - 56)).c := hf.1.symm
          _ = vertex code 1 := by simp [hpattern]
      · calc
          centerB slot = (patternAt (code - 56)).d := hf.2.symm
          _ = vertex code 2 := by simp [hpattern]
    exact checked_AB_forward P hccw slot code hs hlo hhi hodd
      hforward hA hB hcheck
  · have hreverse : centerA slot = vertex code 2 ∧
                     centerB slot = vertex code 1 := by
      constructor
      · calc
          centerA slot = (patternAt (code - 56)).d := hr.2.symm
          _ = vertex code 2 := by simp [hpattern]
      · calc
          centerB slot = (patternAt (code - 56)).c := hr.1.symm
          _ = vertex code 1 := by simp [hpattern]
    exact checked_AB_reverse P hccw slot code hs hlo hhi hodd
      hreverse hA hB hcheck

#print axioms E97A3AllDirections.checked_BC_all_directions
#print axioms E97A3AllDirections.checked_AB_all_directions
end E97A3AllDirections
