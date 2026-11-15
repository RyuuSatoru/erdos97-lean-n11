import CheckReason_PairOrder_CANDIDATE
import ReasonPayload_CANDIDATE
import RowMask_AllCenters_CANDIDATE
import A1A3_MaskSound_Bridge_CANDIDATE
/-!
E97 checkReason -> A1 geometry. No additional axioms.
Proof condition: hcell/hpair identify the decoded payload; realizations give
actual geometric selected rows. Pair ordering and row-mask equality are
proved internally, rather than postulated as extra hypotheses.
The four distinctness conditions relative to centers are intentionally
explicit and must eventually be eliminated using the verified row masks.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97CheckReason
open E97AllowFinite E97Bitmask E97AllowSound E97A1Index E97BlockB

theorem A1_checked_forbids_realization
    (P : Fin 11 → XY) (hccw : StrictCCW11 P)
    (slot code a b x y u v : Nat)
    (hs : slot < 2425500)
    (hcodepos : 0 < code) (hcodeA1 : code ≤ 55)
    (hcenter : pairAt (slot / 44100) = (a, b))
    (hcell : cellData slot = (a, b, x, y, rowMask a x, rowMask b y))
    (hpair : pairAt (code - 1) = (u, v))
    (hx : x < 210) (hy : y < 210)
    (hua : u ≠ a) (hub : u ≠ b)
    (hva : v ≠ a) (hvb : v ≠ b)
    (hA : SelectedRowRealization P (210 * a + x))
    (hB : SelectedRowRealization P (210 * b + y))
    (hcheck : checkReason slot code = true) : False := by
  have hi : slot / 44100 < 55 := by omega
  have hcAB := pair_indices_wellformed (slot / 44100) hi
  rw [hcenter] at hcAB
  have hab : a < b := hcAB.1
  have hb : b < 11 := hcAB.2
  have ha : a < 11 := by omega
  have hci : code - 1 < 55 := by omega
  have hcUV := pair_indices_wellformed (code - 1) hci
  rw [hpair] at hcUV
  have huv : u < v := hcUV.1
  have hv : v < 11 := hcUV.2
  have hu : u < 11 := by omega
  have hp := E97ReasonPayload.a1_payload slot code hs hcodepos hcodeA1 hcheck
  have hmask :
      (containsBits (rowMask a x) ((2 ^ u) ||| (2 ^ v)) &&
       containsBits (rowMask b y) ((2 ^ u) ||| (2 ^ v)) &&
       (alternate a b u v == false)) = true := by
    simpa [hcell, hpair] using hp
  simp only [Bool.and_eq_true] at hmask
  rcases hmask with ⟨⟨hmA, hmB⟩, hbad⟩
  have hbad' : alternate a b u v = false := by
    cases hh : alternate a b u v <;> simp [hh] at hbad ⊢
  have hrowA : rowMask a x = actualRowMask (210 * a + x) :=
    E97RowBridge.all_rows_agree a x ha hx
  have hrowB : rowMask b y = actualRowMask (210 * b + y) :=
    E97RowBridge.all_rows_agree b y hb hy
  have hrA : 210 * a + x < 2310 := by omega
  have hrB : 210 * b + y < 2310 := by omega
  have hcA : (210 * a + x) / 210 = a := by omega
  have hcB : (210 * b + y) / 210 = b := by omega
  have hmA' : containsBits (rowMask a x) (twoBits u v) = true := by
    simpa only [twoBits, bit] using hmA
  have hmB' : containsBits (rowMask b y) (twoBits u v) = true := by
    simpa only [twoBits, bit] using hmB
  exact E97MaskSoundBridge.a1_mask_sound P hccw
    a b x y (210 * a + x) (210 * b + y) u v
    hab hb hrA hrB hcA hcB hu hv hua hub hva hvb (Nat.ne_of_lt huv)
    hA hB hrowA hrowB hmA' hmB' hbad'

#print axioms E97CheckReason.A1_checked_forbids_realization
end E97CheckReason
