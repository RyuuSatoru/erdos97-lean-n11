import A1_IndexAlternation_CANDIDATE

/-!
Remove the final index-to-point distinctness hypothesis from the A1
alternation theorem. Strict positivity of every increasing triple implies
coordinate injectivity, with NO generic-position axiom.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace E97A1Index
open E97BlockB E97A1

/-- Any three strictly counterclockwise indices pick three distinct points. -/
theorem ccw_increasing_triple_pairwise_distinct
    (P : Fin 11 → XY) (hccw : StrictCCW11 P)
    (i j k : Nat) (hij : i < j) (hjk : j < k) (hk : k < 11) :
    P (Fin.ofNat 11 i) ≠ P (Fin.ofNat 11 j) ∧
    P (Fin.ofNat 11 i) ≠ P (Fin.ofNat 11 k) ∧
    P (Fin.ofNat 11 j) ≠ P (Fin.ofNat 11 k) := by
  have hpos := hccw i j k hij hjk hk
  constructor
  · intro heq
    have hz : orient (P (Fin.ofNat 11 i)) (P (Fin.ofNat 11 j))
      (P (Fin.ofNat 11 k)) = 0 := by
      rw [heq]
      dsimp [orient]
      ring
    linarith
  constructor
  · intro heq
    have hz : orient (P (Fin.ofNat 11 i)) (P (Fin.ofNat 11 j))
      (P (Fin.ofNat 11 k)) = 0 := by
      rw [heq]
      dsimp [orient]
      ring
    linarith
  · intro heq
    have hz : orient (P (Fin.ofNat 11 i)) (P (Fin.ofNat 11 j))
      (P (Fin.ofNat 11 k)) = 0 := by
      rw [heq]
      dsimp [orient]
      ring
    linarith

/-- All eleven indexed vertices are pairwise distinct, a consequence
    of the CCW hypothesis alone. -/
theorem ccw11_points_injective
    (P : Fin 11 → XY) (hccw : StrictCCW11 P)
    (i j : Nat) (hi : i < 11) (hj : j < 11) (hij : i ≠ j) :
    P (Fin.ofNat 11 i) ≠ P (Fin.ofNat 11 j) := by
  have hkchoice : ∃ k : Nat, k < 11 ∧ k ≠ i ∧ k ≠ j := by
    by_cases h0 : i ≠ 0 ∧ j ≠ 0
    · exact ⟨0, by omega, by omega, by omega⟩
    · by_cases h1 : i ≠ 1 ∧ j ≠ 1
      · exact ⟨1, by omega, by omega, by omega⟩
      · exact ⟨2, by omega, by omega, by omega⟩
  obtain ⟨k, hk, hki, hkj⟩ := hkchoice
  by_cases hijlt : i < j
  · by_cases hkilt : k < i
    · exact (ccw_increasing_triple_pairwise_distinct P hccw k i j hkilt hijlt hj).2.2
    · by_cases hik : i < k
      · by_cases hkjlt : k < j
        · exact (ccw_increasing_triple_pairwise_distinct P hccw i k j hik hkjlt hj).2.1
        · have hjk : j < k := by omega
          exact (ccw_increasing_triple_pairwise_distinct P hccw i j k hijlt hjk hk).1
      · omega
  · have hjilt : j < i := by omega
    by_cases hkjlt : k < j
    · exact (ccw_increasing_triple_pairwise_distinct P hccw k j i hkjlt hjilt hi).2.2.symm
    · by_cases hjk : j < k
      · by_cases hkilt : k < i
        · exact (ccw_increasing_triple_pairwise_distinct P hccw j k i hjk hkilt hi).2.1.symm
        · have hik : i < k := by omega
          exact (ccw_increasing_triple_pairwise_distinct P hccw j i k hjilt hik hk).1.symm
      · omega

/-- Final geometric A1 crossing result, with NO assumption on
    witness-point distinctness beyond distinct vertex indices. -/
theorem ccw11_A1_crossing_of_two_common_witnesses
    (P : Fin 11 → XY) (hccw : StrictCCW11 P)
    (a b u v : Nat)
    (hab : a < b) (hb : b < 11)
    (hu : u < 11) (hv : v < 11)
    (hua : u ≠ a) (hub : u ≠ b)
    (hva : v ≠ a) (hvb : v ≠ b) (huv : u ≠ v)
    (ha : sqDist (P (Fin.ofNat 11 a)) (P (Fin.ofNat 11 u)) =
          sqDist (P (Fin.ofNat 11 a)) (P (Fin.ofNat 11 v)))
    (hb' : sqDist (P (Fin.ofNat 11 b)) (P (Fin.ofNat 11 u)) =
           sqDist (P (Fin.ofNat 11 b)) (P (Fin.ofNat 11 v))) :
    crossingA1 a b u v = true := by
  have hpoints := ccw11_points_injective P hccw u v hu hv huv
  exact shared_witnesses_crossingA1 P hccw a b u v
    hab hb hu hv hua hub hva hvb hpoints ha hb'

#print axioms E97A1Index.ccw_increasing_triple_pairwise_distinct
#print axioms E97A1Index.ccw11_points_injective
#print axioms E97A1Index.ccw11_A1_crossing_of_two_common_witnesses
end E97A1Index
