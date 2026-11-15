import AllowFiniteReasonCore_CANDIDATE
import BE_A1A3_AllowSound_CANDIDATE
/-!
Soundness transport from the finite generator's masks to existing geometry.
Important: the 2310-row correspondence, witness well-formedness, and
FiveCCW hypotheses remain explicit here. This is NOT yet checkReason soundness.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97MaskSoundBridge
open E97AllowFinite E97Bitmask E97AllowSound E97A1Index E97BlockB E97A3

/-- Both checker implementations use the same Nat bit containment test. -/
theorem same_bit_test (m required : Nat) :
    containsBits m required = containsMask m required := rfl

/-- Checker index alternation equals the established A1 geometric index test. -/
theorem same_alternation (a b u v : Nat) :
    alternate a b u v = crossingA1 a b u v := by
  by_cases hu : a < u ∧ u < b <;>
  by_cases hv : a < v ∧ v < b <;>
  simp [alternate, crossingA1, hu, hv]

/-- Conditional geometry bridge for A1 masks actually emitted by finite checker. -/
theorem a1_mask_sound (P : Fin 11 → XY) (hccw : StrictCCW11 P)
  (a b x y rA rB u v : Nat)
  (hab : a < b) (hb : b < 11)
  (hAr : rA < 2310) (hBr : rB < 2310)
  (hAc : rA / 210 = a) (hBc : rB / 210 = b)
  (hu : u < 11) (hv : v < 11)
  (hua : u ≠ a) (hub : u ≠ b)
  (hva : v ≠ a) (hvb : v ≠ b) (huv : u ≠ v)
  (hA : SelectedRowRealization P rA)
  (hB : SelectedRowRealization P rB)
  (hrowA : rowMask a x = actualRowMask rA)
  (hrowB : rowMask b y = actualRowMask rB)
  (hmA : containsBits (rowMask a x) (twoBits u v) = true)
  (hmB : containsBits (rowMask b y) (twoBits u v) = true)
  (hbad : alternate a b u v = false) : False := by
  have ha : containsMask (actualRowMask rA) (twoBits u v) = true := by
    rw [← hrowA]
    exact hmA
  have hb' : containsMask (actualRowMask rB) (twoBits u v) = true := by
    rw [← hrowB]
    exact hmB
  have hbad' : crossingA1 a b u v = false := by
    simpa only [same_alternation] using hbad
  exact A1_forbidden_actual_pair P hccw a b rA rB u v
    hab hb hAr hBr hAc hBc hu hv hua hub hva hvb huv
    hA hB ha hb' hbad'

/-- Conditional BC form of the exact A3 two/three-bit masks. -/
theorem a3_bc_mask_sound (P : Fin 11 → XY)
  (ip ia ib ic iq x y rB rC : Nat)
  (hfive : FiveCCW (P (Fin.ofNat 11 ip))
      (P (Fin.ofNat 11 ia)) (P (Fin.ofNat 11 ib))
      (P (Fin.ofNat 11 ic)) (P (Fin.ofNat 11 iq)))
  (hBr : rB < 2310) (hCr : rC < 2310)
  (hBc : rB / 210 = ib) (hCc : rC / 210 = ic)
  (hp : ip < 11) (ha : ia < 11) (hb : ib < 11) (hq : iq < 11)
  (hpa : ip ≠ ia) (hqa : iq ≠ ia)
  (hqb : iq ≠ ib) (hab : ia ≠ ib)
  (hB : SelectedRowRealization P rB)
  (hC : SelectedRowRealization P rC)
  (hrowB : rowMask ib x = actualRowMask rB)
  (hrowC : rowMask ic y = actualRowMask rC)
  (hmB : containsBits (rowMask ib x) (twoBits ip ia) = true)
  (hmC : containsBits (rowMask ic y) (threeBits iq ia ib) = true) : False := by
  have hb' : containsMask (actualRowMask rB) (twoBits ip ia) = true := by
    rw [← hrowB]
    exact hmB
  have hc' : containsMask (actualRowMask rC) (threeBits iq ia ib) = true := by
    rw [← hrowC]
    exact hmC
  exact A3_BC_forbidden_actual_masks P ip ia ib ic iq rB rC hfive
    hBr hCr hBc hCc hp ha hb hq hpa hqa hqb hab hB hC hb' hc'

/-- Conditional reflected AB form of exact A3 three/two-bit masks. -/
theorem a3_ab_mask_sound (P : Fin 11 → XY)
  (ip ia ib ic iq x y rA rB : Nat)
  (hfive : FiveCCW (P (Fin.ofNat 11 ip))
      (P (Fin.ofNat 11 ia)) (P (Fin.ofNat 11 ib))
      (P (Fin.ofNat 11 ic)) (P (Fin.ofNat 11 iq)))
  (hAr : rA < 2310) (hBr : rB < 2310)
  (hAc : rA / 210 = ia) (hBc : rB / 210 = ib)
  (hp : ip < 11) (hb : ib < 11) (hc : ic < 11) (hq : iq < 11)
  (hpb : ip ≠ ib) (hpc : ip ≠ ic)
  (hbc : ib ≠ ic) (hqc : iq ≠ ic)
  (hA : SelectedRowRealization P rA)
  (hB : SelectedRowRealization P rB)
  (hrowA : rowMask ia x = actualRowMask rA)
  (hrowB : rowMask ib y = actualRowMask rB)
  (hmA : containsBits (rowMask ia x) (threeBits ip ib ic) = true)
  (hmB : containsBits (rowMask ib y) (twoBits iq ic) = true) : False := by
  have ha' : containsMask (actualRowMask rA) (threeBits ip ib ic) = true := by
    rw [← hrowA]
    exact hmA
  have hb' : containsMask (actualRowMask rB) (twoBits iq ic) = true := by
    rw [← hrowB]
    exact hmB
  exact A3_AB_forbidden_actual_masks P ip ia ib ic iq rA rB hfive
    hAr hBr hAc hBc hp hb hc hq hpb hpc hbc hqc hA hB ha' hb'

#print axioms E97MaskSoundBridge.same_bit_test
#print axioms E97MaskSoundBridge.same_alternation
#print axioms E97MaskSoundBridge.a1_mask_sound
#print axioms E97MaskSoundBridge.a3_bc_mask_sound
#print axioms E97MaskSoundBridge.a3_ab_mask_sound
end E97MaskSoundBridge
