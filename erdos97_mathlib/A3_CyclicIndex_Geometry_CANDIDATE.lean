import A3_FiveIndex_All_CANDIDATE
import A3_CyclicMirror_CANDIDATE
/-! Bridge the 462 verified 5-subsets to all five cyclic rotations in
    StrictCCW11 geometry. Does not yet relate patternAt to the decoded tuple. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97A3Index
open E97BlockB E97A1Index E97A3

def rot5 (i t j : Nat) : Nat := fiveIndex i ((t + j) % 5)

/-- The five actual cyclic rotations of any sorted 5-subset are CCW. -/
theorem rotated_five_ccw (P : Fin 11 → XY) (hccw : StrictCCW11 P)
    (i t : Nat) (hi : i < 462) (ht : t < 5) :
    FiveCCW (P (Fin.ofNat 11 (rot5 i t 0)))
      (P (Fin.ofNat 11 (rot5 i t 1)))
      (P (Fin.ofNat 11 (rot5 i t 2)))
      (P (Fin.ofNat 11 (rot5 i t 3)))
      (P (Fin.ofNat 11 (rot5 i t 4))) := by
  rcases five_valid_of_lt i hi with ⟨h01, h12, h23, h34, h4⟩
  have h : FiveCCW (P (Fin.ofNat 11 (fiveIndex i 0)))
      (P (Fin.ofNat 11 (fiveIndex i 1)))
      (P (Fin.ofNat 11 (fiveIndex i 2)))
      (P (Fin.ofNat 11 (fiveIndex i 3)))
      (P (Fin.ofNat 11 (fiveIndex i 4))) :=
    FiveCCW.of_increasing P hccw
      (fiveIndex i 0) (fiveIndex i 1) (fiveIndex i 2)
      (fiveIndex i 3) (fiveIndex i 4)
      h01 h12 h23 h34 h4
  rcases h.five_rotations with ⟨h0, h1, h2, h3, h4'⟩
  interval_cases t
  · simpa [rot5] using h0
  · simpa [rot5] using h1
  · simpa [rot5] using h2
  · simpa [rot5] using h3
  · simpa [rot5] using h4'

/-- The A3 code 56..4675 determines a 5-subset and a rotation;
    it therefore supplies FiveCCW without assuming it. -/
theorem code_five_ccw (P : Fin 11 → XY) (hccw : StrictCCW11 P)
    (code : Nat) (hcode : 55 < code) (hmax : code ≤ 4675) :
    FiveCCW
      (P (Fin.ofNat 11 (rot5 ((code - 56) / 10) (((code - 56) % 10) / 2) 0)))
      (P (Fin.ofNat 11 (rot5 ((code - 56) / 10) (((code - 56) % 10) / 2) 1)))
      (P (Fin.ofNat 11 (rot5 ((code - 56) / 10) (((code - 56) % 10) / 2) 2)))
      (P (Fin.ofNat 11 (rot5 ((code - 56) / 10) (((code - 56) % 10) / 2) 3)))
      (P (Fin.ofNat 11 (rot5 ((code - 56) / 10) (((code - 56) % 10) / 2) 4))) := by
  have hi : (code - 56) / 10 < 462 := by omega
  have ht : ((code - 56) % 10) / 2 < 5 := by omega
  exact rotated_five_ccw P hccw _ _ hi ht

#print axioms E97A3Index.rotated_five_ccw
#print axioms E97A3Index.code_five_ccw
end E97A3Index
