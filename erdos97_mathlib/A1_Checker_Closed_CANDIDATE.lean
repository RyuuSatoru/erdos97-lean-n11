import A1_CenterExclusion_CANDIDATE
import CheckReason_A1_Sound_CANDIDATE
import CellData_Slot_Decode_CANDIDATE
/-!
Discharges the four distinctness hypotheses of the previous conditional A1
checker theorem using real-row masks and the row's excluded center.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97A1Closed
open E97AllowFinite E97CellSlot E97CheckReason E97BlockB
open E97MaskWitness E97Bitmask E97AllowSound

private theorem row_index_lt (c r : Nat) (hc : c < 11) (hr : r < 210) :
    210 * c + r < 2310 := by omega

private theorem row_index_center (c r : Nat) (hr : r < 210) :
    (210 * c + r) / 210 = c := by omega

/-- A positive A1 rejection cannot coexist with realizations of both real rows.
The former explicit center-distinctness assumptions are now proved internally. -/
theorem checked_A1_no_distinctness
    (P : Fin 11 → XY) (hccw : E97A1Index.StrictCCW11 P)
    (slot code : Nat) (hs : slot < 2425500)
    (hpos : 0 < code) (hA1 : code ≤ 55)
    (hA : SelectedRowRealization P (210 * centerA slot + rowX slot))
    (hB : SelectedRowRealization P (210 * centerB slot + rowY slot))
    (hcheck : checkReason slot code = true) : False := by
  let a := centerA slot
  let b := centerB slot
  let x := rowX slot
  let y := rowY slot
  let u := (pairAt (code - 1)).1
  let v := (pairAt (code - 1)).2
  have hbounds := slot_bounds slot hs
  have hab : a < b := hbounds.1
  have hb : b < 11 := hbounds.2.1
  have ha : a < 11 := by omega
  have hx : x < 210 := hbounds.2.2.1
  have hy : y < 210 := hbounds.2.2.2
  have hi : code - 1 < 55 := by omega
  have hpairs := pair_indices_wellformed (code - 1) hi
  have huvlt : u < v := hpairs.1
  have hu : u < 11 := by omega
  have hv : v < 11 := hpairs.2
  have huv : u ≠ v := Nat.ne_of_lt huvlt
  have hrA : 210 * a + x < 2310 := row_index_lt a x ha hx
  have hrB : 210 * b + y < 2310 := row_index_lt b y hb hy
  have hcA : (210 * a + x) / 210 = a := row_index_center a x hx
  have hcB : (210 * b + y) / 210 = b := row_index_center b y hy
  have hcenter : pairAt (slot / 44100) = (a, b) := by
    cases h : pairAt (slot / 44100) with
    | mk aa bb => simp [a, b, centerA, centerB, h]
  have hpair : pairAt (code - 1) = (u, v) := by
    cases h : pairAt (code - 1) with
    | mk uu vv => simp [u, v, h]
  have hcell : cellData slot = (a, b, x, y, rowMask a x, rowMask b y) :=
    cellData_exact slot
  have hraw := E97ReasonPayload.a1_payload slot code hs hpos hA1 hcheck
  have hmask :
      (containsBits (rowMask a x) ((2 ^ u) ||| (2 ^ v)) &&
       containsBits (rowMask b y) ((2 ^ u) ||| (2 ^ v)) &&
       (alternate a b u v == false)) = true := by
    simpa [hcell, hpair] using hraw
  simp only [Bool.and_eq_true] at hmask
  rcases hmask with ⟨⟨hmA, hmB⟩, _⟩
  have hrowA : rowMask a x = actualRowMask (210 * a + x) :=
    E97RowBridge.all_rows_agree a x ha hx
  have hrowB : rowMask b y = actualRowMask (210 * b + y) :=
    E97RowBridge.all_rows_agree b y hb hy
  have hmaskA : containsMask (actualRowMask (210 * a + x)) (twoBits u v) = true := by
    rw [← hrowA]
    exact hmA
  have hmaskB : containsMask (actualRowMask (210 * b + y)) (twoBits u v) = true := by
    rw [← hrowB]
    exact hmB
  obtain ⟨huA, hvA⟩ := actual_pair_mask_members (210 * a + x) u v
    hrA hu hv huv hmaskA
  obtain ⟨huB, hvB⟩ := actual_pair_mask_members (210 * b + y) u v
    hrB hu hv huv hmaskB
  have hua : u ≠ a := by
    have h := E97A1CenterExclusion.witness_ne_center (210 * a + x) u hrA huA
    simpa only [hcA] using h
  have hub : u ≠ b := by
    have h := E97A1CenterExclusion.witness_ne_center (210 * b + y) u hrB huB
    simpa only [hcB] using h
  have hva : v ≠ a := by
    have h := E97A1CenterExclusion.witness_ne_center (210 * a + x) v hrA hvA
    simpa only [hcA] using h
  have hvb : v ≠ b := by
    have h := E97A1CenterExclusion.witness_ne_center (210 * b + y) v hrB hvB
    simpa only [hcB] using h
  have hA' : SelectedRowRealization P (210 * a + x) := by
    simpa only [a, x] using hA
  have hB' : SelectedRowRealization P (210 * b + y) := by
    simpa only [b, y] using hB
  exact E97CheckReason.A1_checked_forbids_realization
    P hccw slot code a b x y u v hs hpos hA1
    hcenter hcell hpair hx hy hua hub hva hvb hA' hB' hcheck

#print axioms E97A1Closed.checked_A1_no_distinctness
end E97A1Closed
