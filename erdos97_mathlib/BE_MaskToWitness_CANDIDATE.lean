import BE_ActualRowBitmask_CANDIDATE

/-!
E97 n=11: the real `getRow` mask implies membership in the *actual*
four-witness set. This bridges Boolean bit arithmetic to row semantics.
No theorem here says the complete C++ `allow` table has been checked by Lean.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
-- Redundant simp-hint diagnostics have no bearing on kernel soundness.
set_option linter.unusedSimpArgs false

namespace E97MaskWitness
open E97Bitmask E97A2Rows E97A2Prefix

/-- Boolean conjunction is true only when both factors are true.
    This does not depend on the lemma names exposed by Mathlib. -/
private theorem and_true_parts {x y : Bool} (h : (x && y) = true) :
    x = true ∧ y = true := by
  cases x <;> cases y <;> simp_all

/-- Each in-range actual row has a mask in the 11-bit range. -/
theorem actual_row_mask_lt (p : Nat) (hp : p < 2310) :
    actualRowMask p < 2048 := by
  have h := (List.all_eq_true.mp allActualRowMasksOK) p
    (List.mem_range.mpr hp)
  unfold actualRowMaskOK at h
  rcases hrow : decodedWitnesses p with ⟨a, b, c, d⟩
  simp only [hrow] at h
  have hbound := (and_true_parts h).1
  simpa only [decide_eq_true_eq] using hbound

/-- A bit of the true row mask is set if and only if the decoded
witness set of `getRow` contains that vertex. -/
theorem actual_row_hasBit_iff (p u : Nat)
    (hp : p < 2310) (hu : u < 11) :
    hasBit (actualRowMask p) u = true ↔ u ∈ rowWitnessSet p := by
  have h := (List.all_eq_true.mp allActualRowMasksOK) p
    (List.mem_range.mpr hp)
  unfold actualRowMaskOK at h
  rcases hrow : decodedWitnesses p with ⟨a, b, c, d⟩
  simp only [hrow] at h
  have hscan := (and_true_parts h).2
  have hbit := (List.all_eq_true.mp hscan) u (List.mem_range.mpr hu)
  have hbeq : hasBit (actualRowMask p) u =
      decide (u = a ∨ u = b ∨ u = c ∨ u = d) := by
    simpa using hbit
  rw [hbeq]
  simp [rowWitnessSet, hrow]

/-- The previously kernel-checked sorted pair statement, now for
any order of two *distinct* requested vertices. -/
theorem pair_inclusion_any (m u v : Nat)
    (hm : m < 2048) (hu : u < 11) (hv : v < 11) (hne : u ≠ v) :
    containsMask m (twoBits u v) = (hasBit m u && hasBit m v) := by
  by_cases huv : u < v
  · exact pair_inclusion_exact m u v hm hu hv huv
  · have hvu : v < u := by omega
    have h := pair_inclusion_exact m v u hm hv hu hvu
    simpa [twoBits, Nat.or_comm, Bool.and_comm] using h

/-- Exhaustive case split over the six permutations of three distinct
vertices, reducing them to `triple_inclusion_exact` for sorted indices. -/
theorem triple_inclusion_any (m u v w : Nat)
    (hm : m < 2048) (hu : u < 11) (hv : v < 11) (hw : w < 11)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    containsMask m (threeBits u v w) =
      (hasBit m u && hasBit m v && hasBit m w) := by
  have hcases :
      (u < v ∧ v < w) ∨ (u < w ∧ w < v) ∨
      (v < u ∧ u < w) ∨ (v < w ∧ w < u) ∨
      (w < u ∧ u < v) ∨ (w < v ∧ v < u) := by
    omega
  rcases hcases with h | h | h | h | h | h
  · exact triple_inclusion_exact m u v w hm hu hv hw h.1 h.2
  · have hh := triple_inclusion_exact m u w v hm hu hw hv h.1 h.2
    simpa [threeBits, Nat.or_assoc, Nat.or_comm, Nat.or_left_comm,
      Bool.and_assoc, Bool.and_comm, Bool.and_left_comm] using hh
  · have hh := triple_inclusion_exact m v u w hm hv hu hw h.1 h.2
    simpa [threeBits, Nat.or_assoc, Nat.or_comm, Nat.or_left_comm,
      Bool.and_assoc, Bool.and_comm, Bool.and_left_comm] using hh
  · have hh := triple_inclusion_exact m v w u hm hv hw hu h.1 h.2
    simpa [threeBits, Nat.or_assoc, Nat.or_comm, Nat.or_left_comm,
      Bool.and_assoc, Bool.and_comm, Bool.and_left_comm] using hh
  · have hh := triple_inclusion_exact m w u v hm hw hu hv h.1 h.2
    simpa [threeBits, Nat.or_assoc, Nat.or_comm, Nat.or_left_comm,
      Bool.and_assoc, Bool.and_comm, Bool.and_left_comm] using hh
  · have hh := triple_inclusion_exact m w v u hm hw hv hu h.1 h.2
    simpa [threeBits, Nat.or_assoc, Nat.or_comm, Nat.or_left_comm,
      Bool.and_assoc, Bool.and_comm, Bool.and_left_comm] using hh

/-- A true C++ two-bit inclusion test witnesses *both* actual row members. -/
theorem actual_pair_mask_members (p u v : Nat)
    (hp : p < 2310) (hu : u < 11) (hv : v < 11) (hne : u ≠ v)
    (hmask : containsMask (actualRowMask p) (twoBits u v) = true) :
    u ∈ rowWitnessSet p ∧ v ∈ rowWitnessSet p := by
  have h := pair_inclusion_any (actualRowMask p) u v
    (actual_row_mask_lt p hp) hu hv hne
  rw [h] at hmask
  have hh := and_true_parts hmask
  constructor
  · exact (actual_row_hasBit_iff p u hp hu).mp hh.1
  · exact (actual_row_hasBit_iff p v hp hv).mp hh.2

/-- A true C++ three-bit inclusion test witnesses *all three* row members.
The three indices need not be in sorted order, as in cyclic A3 patterns. -/
theorem actual_triple_mask_members (p u v w : Nat)
    (hp : p < 2310) (hu : u < 11) (hv : v < 11) (hw : w < 11)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hmask : containsMask (actualRowMask p) (threeBits u v w) = true) :
    u ∈ rowWitnessSet p ∧ v ∈ rowWitnessSet p ∧ w ∈ rowWitnessSet p := by
  have h := triple_inclusion_any (actualRowMask p) u v w
    (actual_row_mask_lt p hp) hu hv hw huv huw hvw
  rw [h] at hmask
  have hh := and_true_parts hmask
  have hpair := and_true_parts hh.1
  constructor
  · exact (actual_row_hasBit_iff p u hp hu).mp hpair.1
  constructor
  · exact (actual_row_hasBit_iff p v hp hv).mp hpair.2
  · exact (actual_row_hasBit_iff p w hp hw).mp hh.2

#print axioms E97MaskWitness.actual_row_mask_lt
#print axioms E97MaskWitness.actual_row_hasBit_iff
#print axioms E97MaskWitness.pair_inclusion_any
#print axioms E97MaskWitness.triple_inclusion_any
#print axioms E97MaskWitness.actual_pair_mask_members
#print axioms E97MaskWitness.actual_triple_mask_members
end E97MaskWitness
