import E97_RowRealization_Core
import BE_MaskToWitness_CANDIDATE
import A1_PointDistinct_CANDIDATE
import A3_RowPatternBridge_CANDIDATE

/-!
Erdos #97, n=11: exact geometric soundness of the A1 and both A3
row-pair rejection *witnesses*, using the true getRow data and masks.

A rejection witness includes two actual row IDs, their true centers,
a mask predicate, and for A3 a FiveCCW cyclic geometric pattern.
The next obligation is formal soundness of the finite C++ allow-table
GENERATOR: every zero entry must supply one of these witnesses.
No claim of Lean end-to-end certification is made here.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

namespace E97AllowSound
open E97BlockB E97Bitmask E97A2Prefix E97A1Index
open E97MaskWitness E97A3

/- The equal-radius condition for an *actual* row at its decoded center.
Unlike an arbitrary SelectedRowEq, this cannot be attached to another center. -/
/-- True A1 geometric crossing, starting from the real two-bit mask tests
of two rows centered at a<b. -/
theorem A1_crossing_of_actual_masks
    (P : Fin 11 → XY) (hccw : StrictCCW11 P)
    (a b rA rB u v : Nat)
    (hab : a < b) (hb : b < 11)
    (hAr : rA < 2310) (hBr : rB < 2310)
    (hAc : rA / 210 = a) (hBc : rB / 210 = b)
    (hu : u < 11) (hv : v < 11)
    (hua : u ≠ a) (hub : u ≠ b)
    (hva : v ≠ a) (hvb : v ≠ b) (huv : u ≠ v)
    (hA : SelectedRowRealization P rA)
    (hB : SelectedRowRealization P rB)
    (hmA : containsMask (actualRowMask rA) (twoBits u v) = true)
    (hmB : containsMask (actualRowMask rB) (twoBits u v) = true) :
    crossingA1 a b u v = true := by
  obtain ⟨huA, hvA⟩ := actual_pair_mask_members rA u v hAr hu hv huv hmA
  obtain ⟨huB, hvB⟩ := actual_pair_mask_members rB u v hBr hu hv huv hmB
  have hAeq : SelectedRowEq P a (rowWitnessSet rA) := by
    simpa only [SelectedRowRealization, hAc] using hA
  have hBeq : SelectedRowEq P b (rowWitnessSet rB) := by
    simpa only [SelectedRowRealization, hBc] using hB
  exact ccw11_A1_crossing_of_two_common_witnesses
    P hccw a b u v hab hb hu hv hua hub hva hvb huv
    (hAeq u v huA hvA) (hBeq u v huB hvB)

/-- Rejecting the actual two-row pair because A1 requires non-crossing
is sound: no strictly CCW 11-gon can realize it. -/
theorem A1_forbidden_actual_pair
    (P : Fin 11 → XY) (hccw : StrictCCW11 P)
    (a b rA rB u v : Nat)
    (hab : a < b) (hb : b < 11)
    (hAr : rA < 2310) (hBr : rB < 2310)
    (hAc : rA / 210 = a) (hBc : rB / 210 = b)
    (hu : u < 11) (hv : v < 11)
    (hua : u ≠ a) (hub : u ≠ b)
    (hva : v ≠ a) (hvb : v ≠ b) (huv : u ≠ v)
    (hA : SelectedRowRealization P rA)
    (hB : SelectedRowRealization P rB)
    (hmA : containsMask (actualRowMask rA) (twoBits u v) = true)
    (hmB : containsMask (actualRowMask rB) (twoBits u v) = true)
    (hbad : crossingA1 a b u v = false) : False := by
  have hgood := A1_crossing_of_actual_masks P hccw a b rA rB u v
    hab hb hAr hBr hAc hBc hu hv hua hub hva hvb huv
    hA hB hmA hmB
  exact Bool.false_ne_true (hbad.symm.trans hgood)

/-- True C++ A3 BC pattern: B-row contains P,A and C-row Q,A,B.
No equality of lengths is postulated away from the actual row centers. -/
theorem A3_BC_forbidden_actual_masks
    (P : Fin 11 → XY)
    (ip ia ib ic iq rB rC : Nat)
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
    (hmB : containsMask (actualRowMask rB) (twoBits ip ia) = true)
    (hmC : containsMask (actualRowMask rC) (threeBits iq ia ib) = true) :
    False := by
  obtain ⟨hpB, haB⟩ := actual_pair_mask_members rB ip ia
    hBr hp ha hpa hmB
  obtain ⟨hqC, haC, hbC⟩ := actual_triple_mask_members rC iq ia ib
    hCr hq ha hb hqa hqb hab hmC
  have hBeq : SelectedRowEq P ib (rowWitnessSet rB) := by
    simpa only [SelectedRowRealization, hBc] using hB
  have hCeq : SelectedRowEq P ic (rowWitnessSet rC) := by
    simpa only [SelectedRowRealization, hCc] using hC
  exact selected_rows_forbid_BC P ip ia ib ic iq hfive
    (rowWitnessSet rB) (rowWitnessSet rC)
    hBeq hCeq hpB haB hqC haC hbC

/-- True C++ reflected A3 AB pattern: A-row contains P,B,C and
B-row contains Q,C. Covers any cyclic order of the five distinct indices. -/
theorem A3_AB_forbidden_actual_masks
    (P : Fin 11 → XY)
    (ip ia ib ic iq rA rB : Nat)
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
    (hmA : containsMask (actualRowMask rA) (threeBits ip ib ic) = true)
    (hmB : containsMask (actualRowMask rB) (twoBits iq ic) = true) :
    False := by
  obtain ⟨hpA, hbA, hcA⟩ := actual_triple_mask_members rA ip ib ic
    hAr hp hb hc hpb hpc hbc hmA
  obtain ⟨hqB, hcB⟩ := actual_pair_mask_members rB iq ic
    hBr hq hc hqc hmB
  have hAeq : SelectedRowEq P ia (rowWitnessSet rA) := by
    simpa only [SelectedRowRealization, hAc] using hA
  have hBeq : SelectedRowEq P ib (rowWitnessSet rB) := by
    simpa only [SelectedRowRealization, hBc] using hB
  exact selected_rows_forbid_AB P ip ia ib ic iq hfive
    (rowWitnessSet rA) (rowWitnessSet rB)
    hAeq hBeq hpA hbA hcA hqB hcB

#print axioms E97AllowSound.A1_crossing_of_actual_masks
#print axioms E97AllowSound.A1_forbidden_actual_pair
#print axioms E97AllowSound.A3_BC_forbidden_actual_masks
#print axioms E97AllowSound.A3_AB_forbidden_actual_masks
end E97AllowSound
