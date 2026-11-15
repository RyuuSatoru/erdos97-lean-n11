import A3_CellData_ForwardTransport_CANDIDATE
import CheckReason_A3_ReversePayload_CANDIDATE
/-!
Reversed-center geometric transport for both A3 code parities.
The two row realizations are supplied in the *actual slot order*.
No new axioms, no unproved geometry, no untrusted U16 certificate.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97A3CellReverse
open E97AllowFinite E97CellSlot E97A3Pattern E97A3ReversePayload
open E97BlockB E97AllowSound E97Bitmask E97A3Index E97A3

/-! Small arithmetic certificates, deliberately proved outside the large
geometric context so `omega` sees only the two necessary hypotheses. -/
private theorem row_address_below_2310 (c r : Nat)
    (hc : c < 11) (hr : r < 210) : 210 * c + r < 2310 := by
  omega

private theorem row_address_center (c r : Nat) (hr : r < 210) :
    (210 * c + r) / 210 = c := by
  omega

/-- BC: centerA is geometric C and centerB is geometric B. -/
theorem checked_BC_reverse (P : Fin 11 → XY)
    (hccw : E97A1Index.StrictCCW11 P)
    (slot code : Nat) (hs : slot < 2425500)
    (hlo : 55 < code) (hhi : code ≤ 4675)
    (heven : (code - 56) % 2 = 0)
    (hreverse : centerA slot = vertex code 3 ∧
                centerB slot = vertex code 2)
    (hA : SelectedRowRealization P (210 * centerA slot + rowX slot))
    (hB : SelectedRowRealization P (210 * centerB slot + rowY slot))
    (hcheck : checkReason slot code = true) : False := by
  obtain ⟨hp, ha, hb, hc, hq, hpa, hqa, hqb, hab,
          _hpb, _hpc, _hbc, _hqc⟩ := code_vertices_valid code hlo hhi
  rcases hreverse with ⟨hca, hcb⟩
  have hpattern : patternAt (code - 56) =
      ⟨vertex code 2, vertex code 3,
       twoBits (vertex code 0) (vertex code 1),
       threeBits (vertex code 4) (vertex code 1) (vertex code 2)⟩ := by
    simpa only [vertex] using patternAt_bc (code - 56) heven
  have hroute : (patternAt (code - 56)).c = centerB slot ∧
                (patternAt (code - 56)).d = centerA slot := by
    constructor
    · simp [hpattern, hcb]
    · simp [hpattern, hca]
  have hmask := checked_reverse_masks slot code hs hlo hhi hcheck hroute
  have hmB : containsBits (rowMask (vertex code 2) (rowY slot))
      (twoBits (vertex code 0) (vertex code 1)) = true := by
    simpa only [hcb, hpattern] using hmask.1
  have hmC : containsBits (rowMask (vertex code 3) (rowX slot))
      (threeBits (vertex code 4) (vertex code 1) (vertex code 2)) = true := by
    simpa only [hca, hpattern] using hmask.2
  have hfive : FiveCCW
      (P (Fin.ofNat 11 (vertex code 0)))
      (P (Fin.ofNat 11 (vertex code 1)))
      (P (Fin.ofNat 11 (vertex code 2)))
      (P (Fin.ofNat 11 (vertex code 3)))
      (P (Fin.ofNat 11 (vertex code 4))) := by
    simpa only [vertex] using code_five_ccw P hccw code hlo hhi
  have hx : rowX slot < 210 := (slot_bounds slot hs).2.2.1
  have hy : rowY slot < 210 := (slot_bounds slot hs).2.2.2
  have hB' : SelectedRowRealization P (210 * vertex code 2 + rowY slot) := by
    simpa only [hcb] using hB
  have hC' : SelectedRowRealization P (210 * vertex code 3 + rowX slot) := by
    simpa only [hca] using hA
  have hrowB : rowMask (vertex code 2) (rowY slot) =
      actualRowMask (210 * vertex code 2 + rowY slot) :=
    E97RowBridge.all_rows_agree _ _ hb hy
  have hrowC : rowMask (vertex code 3) (rowX slot) =
      actualRowMask (210 * vertex code 3 + rowX slot) :=
    E97RowBridge.all_rows_agree _ _ hc hx
  have hrB : 210 * vertex code 2 + rowY slot < 2310 :=
    row_address_below_2310 (vertex code 2) (rowY slot) hb hy
  have hrC : 210 * vertex code 3 + rowX slot < 2310 :=
    row_address_below_2310 (vertex code 3) (rowX slot) hc hx
  have hcB : (210 * vertex code 2 + rowY slot) / 210 = vertex code 2 :=
    row_address_center (vertex code 2) (rowY slot) hy
  have hcC : (210 * vertex code 3 + rowX slot) / 210 = vertex code 3 :=
    row_address_center (vertex code 3) (rowX slot) hx
  exact E97MaskSoundBridge.a3_bc_mask_sound P
    (vertex code 0) (vertex code 1) (vertex code 2)
    (vertex code 3) (vertex code 4)
    (rowY slot) (rowX slot)
    (210 * vertex code 2 + rowY slot)
    (210 * vertex code 3 + rowX slot)
    hfive hrB hrC hcB hcC hp ha hb hq hpa hqa hqb hab
    hB' hC' hrowB hrowC hmB hmC

/-- AB: centerA is geometric B and centerB is geometric A. -/
theorem checked_AB_reverse (P : Fin 11 → XY)
    (hccw : E97A1Index.StrictCCW11 P)
    (slot code : Nat) (hs : slot < 2425500)
    (hlo : 55 < code) (hhi : code ≤ 4675)
    (hodd : (code - 56) % 2 ≠ 0)
    (hreverse : centerA slot = vertex code 2 ∧
                centerB slot = vertex code 1)
    (hA : SelectedRowRealization P (210 * centerA slot + rowX slot))
    (hB : SelectedRowRealization P (210 * centerB slot + rowY slot))
    (hcheck : checkReason slot code = true) : False := by
  obtain ⟨hp, ha, hb, hc, hq, _hpa, _hqa, _hqb, _hab,
          hpb, hpc, hbc, hqc⟩ := code_vertices_valid code hlo hhi
  rcases hreverse with ⟨hca, hcb⟩
  have hpattern : patternAt (code - 56) =
      ⟨vertex code 1, vertex code 2,
       threeBits (vertex code 0) (vertex code 2) (vertex code 3),
       twoBits (vertex code 4) (vertex code 3)⟩ := by
    simpa only [vertex] using patternAt_ab (code - 56) hodd
  have hroute : (patternAt (code - 56)).c = centerB slot ∧
                (patternAt (code - 56)).d = centerA slot := by
    constructor
    · simp [hpattern, hcb]
    · simp [hpattern, hca]
  have hmask := checked_reverse_masks slot code hs hlo hhi hcheck hroute
  have hmA : containsBits (rowMask (vertex code 1) (rowY slot))
      (threeBits (vertex code 0) (vertex code 2) (vertex code 3)) = true := by
    simpa only [hcb, hpattern] using hmask.1
  have hmB : containsBits (rowMask (vertex code 2) (rowX slot))
      (twoBits (vertex code 4) (vertex code 3)) = true := by
    simpa only [hca, hpattern] using hmask.2
  have hfive : FiveCCW
      (P (Fin.ofNat 11 (vertex code 0)))
      (P (Fin.ofNat 11 (vertex code 1)))
      (P (Fin.ofNat 11 (vertex code 2)))
      (P (Fin.ofNat 11 (vertex code 3)))
      (P (Fin.ofNat 11 (vertex code 4))) := by
    simpa only [vertex] using code_five_ccw P hccw code hlo hhi
  have hx : rowX slot < 210 := (slot_bounds slot hs).2.2.1
  have hy : rowY slot < 210 := (slot_bounds slot hs).2.2.2
  have hA' : SelectedRowRealization P (210 * vertex code 1 + rowY slot) := by
    simpa only [hcb] using hB
  have hB' : SelectedRowRealization P (210 * vertex code 2 + rowX slot) := by
    simpa only [hca] using hA
  have hrowA : rowMask (vertex code 1) (rowY slot) =
      actualRowMask (210 * vertex code 1 + rowY slot) :=
    E97RowBridge.all_rows_agree _ _ ha hy
  have hrowB : rowMask (vertex code 2) (rowX slot) =
      actualRowMask (210 * vertex code 2 + rowX slot) :=
    E97RowBridge.all_rows_agree _ _ hb hx
  have hrA : 210 * vertex code 1 + rowY slot < 2310 :=
    row_address_below_2310 (vertex code 1) (rowY slot) ha hy
  have hrB : 210 * vertex code 2 + rowX slot < 2310 :=
    row_address_below_2310 (vertex code 2) (rowX slot) hb hx
  have hcA : (210 * vertex code 1 + rowY slot) / 210 = vertex code 1 :=
    row_address_center (vertex code 1) (rowY slot) hy
  have hcB : (210 * vertex code 2 + rowX slot) / 210 = vertex code 2 :=
    row_address_center (vertex code 2) (rowX slot) hx
  exact E97MaskSoundBridge.a3_ab_mask_sound P
    (vertex code 0) (vertex code 1) (vertex code 2)
    (vertex code 3) (vertex code 4)
    (rowY slot) (rowX slot)
    (210 * vertex code 1 + rowY slot)
    (210 * vertex code 2 + rowX slot)
    hfive hrA hrB hcA hcB hp hb hc hq hpb hpc hbc hqc
    hA' hB' hrowA hrowB hmA hmB

#print axioms E97A3CellReverse.checked_BC_reverse
#print axioms E97A3CellReverse.checked_AB_reverse
end E97A3CellReverse
