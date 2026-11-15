import ReasonPayload_CANDIDATE
import RowMask_AllCenters_CANDIDATE
import A1A3_MaskSound_Bridge_CANDIDATE
/-!
E97 checkReason -> A3 geometric rejection, in the BC and AB cases.
The FiveCCW hypothesis and exact decoded pattern identity are still explicit:
future work must derive them from a StrictCCW11 configuration and patternAt.
No additional axioms.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97CheckReason
open E97AllowFinite E97Bitmask E97AllowSound E97A1Index E97BlockB E97A3

theorem A3_BC_checked_forbids_realization
    (P : Fin 11 → XY)
    (slot code ip ia ib ic iq x y : Nat)
    (hs : slot < 2425500)
    (hcodeA3 : 55 < code) (hcodeMax : code ≤ 4675)
    (hcell : cellData slot =
      (ib, ic, x, y, rowMask ib x, rowMask ic y))
    (hpattern : patternAt (code - 56) =
      ⟨ib, ic, twoBits ip ia, threeBits iq ia ib⟩)
    (hx : x < 210) (hy : y < 210)
    (hp : ip < 11) (ha : ia < 11)
    (hb : ib < 11) (hc : ic < 11) (hq : iq < 11)
    (hpa : ip ≠ ia) (hqa : iq ≠ ia) (hqb : iq ≠ ib)
    (hab : ia ≠ ib)
    (hfive : FiveCCW (P (Fin.ofNat 11 ip))
      (P (Fin.ofNat 11 ia)) (P (Fin.ofNat 11 ib))
      (P (Fin.ofNat 11 ic)) (P (Fin.ofNat 11 iq)))
    (hB : SelectedRowRealization P (210 * ib + x))
    (hC : SelectedRowRealization P (210 * ic + y))
    (hcheck : checkReason slot code = true) : False := by
  have hpayload := E97ReasonPayload.a3_payload slot code hs hcodeA3 hcodeMax hcheck
  have hmask :
      (containsBits (rowMask ib x) (twoBits ip ia) &&
       containsBits (rowMask ic y) (threeBits iq ia ib)) = true := by
    simpa [hcell, hpattern] using hpayload
  simp only [Bool.and_eq_true] at hmask
  rcases hmask with ⟨hmB, hmC⟩
  have hrowB : rowMask ib x = actualRowMask (210 * ib + x) :=
    E97RowBridge.all_rows_agree ib x hb hx
  have hrowC : rowMask ic y = actualRowMask (210 * ic + y) :=
    E97RowBridge.all_rows_agree ic y hc hy
  have hrB : 210 * ib + x < 2310 := by omega
  have hrC : 210 * ic + y < 2310 := by omega
  have hcB : (210 * ib + x) / 210 = ib := by omega
  have hcC : (210 * ic + y) / 210 = ic := by omega
  exact E97MaskSoundBridge.a3_bc_mask_sound P
    ip ia ib ic iq x y (210 * ib + x) (210 * ic + y)
    hfive hrB hrC hcB hcC hp ha hb hq hpa hqa hqb hab
    hB hC hrowB hrowC hmB hmC

theorem A3_AB_checked_forbids_realization
    (P : Fin 11 → XY)
    (slot code ip ia ib ic iq x y : Nat)
    (hs : slot < 2425500)
    (hcodeA3 : 55 < code) (hcodeMax : code ≤ 4675)
    (hcell : cellData slot =
      (ia, ib, x, y, rowMask ia x, rowMask ib y))
    (hpattern : patternAt (code - 56) =
      ⟨ia, ib, threeBits ip ib ic, twoBits iq ic⟩)
    (hx : x < 210) (hy : y < 210)
    (hp : ip < 11) (ha : ia < 11)
    (hb : ib < 11) (hc : ic < 11) (hq : iq < 11)
    (hpb : ip ≠ ib) (hpc : ip ≠ ic) (hbc : ib ≠ ic)
    (hqc : iq ≠ ic)
    (hfive : FiveCCW (P (Fin.ofNat 11 ip))
      (P (Fin.ofNat 11 ia)) (P (Fin.ofNat 11 ib))
      (P (Fin.ofNat 11 ic)) (P (Fin.ofNat 11 iq)))
    (hA : SelectedRowRealization P (210 * ia + x))
    (hB : SelectedRowRealization P (210 * ib + y))
    (hcheck : checkReason slot code = true) : False := by
  have hpayload := E97ReasonPayload.a3_payload slot code hs hcodeA3 hcodeMax hcheck
  have hmask :
      (containsBits (rowMask ia x) (threeBits ip ib ic) &&
       containsBits (rowMask ib y) (twoBits iq ic)) = true := by
    simpa [hcell, hpattern] using hpayload
  simp only [Bool.and_eq_true] at hmask
  rcases hmask with ⟨hmA, hmB⟩
  have hrowA : rowMask ia x = actualRowMask (210 * ia + x) :=
    E97RowBridge.all_rows_agree ia x ha hx
  have hrowB : rowMask ib y = actualRowMask (210 * ib + y) :=
    E97RowBridge.all_rows_agree ib y hb hy
  have hrA : 210 * ia + x < 2310 := by omega
  have hrB : 210 * ib + y < 2310 := by omega
  have hcA : (210 * ia + x) / 210 = ia := by omega
  have hcB : (210 * ib + y) / 210 = ib := by omega
  exact E97MaskSoundBridge.a3_ab_mask_sound P
    ip ia ib ic iq x y (210 * ia + x) (210 * ib + y)
    hfive hrA hrB hcA hcB hp hb hc hq hpb hpc hbc hqc
    hA hB hrowA hrowB hmA hmB

#print axioms E97CheckReason.A3_BC_checked_forbids_realization
#print axioms E97CheckReason.A3_AB_checked_forbids_realization
end E97CheckReason
