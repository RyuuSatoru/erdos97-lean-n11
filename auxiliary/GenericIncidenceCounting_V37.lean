import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace E97Structural37
open scoped BigOperators

def incomingCenters (n : Nat) (rows : Nat → Finset Nat) (v : Nat) : Finset Nat :=
  (Finset.range n).filter (fun c => v ∈ rows c)

def pairCenters (n : Nat) (rows : Nat → Finset Nat) (u v : Nat) : Finset Nat :=
  (Finset.range n).filter (fun c => u ∈ rows c ∧ v ∈ rows c)

theorem local_partners (n k : Nat) (rows : Nat → Finset Nat) (c v : Nat)
    (hcard : (rows c).card = k) (hbound : rows c ⊆ Finset.range n) :
    (∑ w ∈ (Finset.range n).erase v,
      if v ∈ rows c ∧ w ∈ rows c then (1 : Nat) else 0) =
      (k - 1) * (if v ∈ rows c then 1 else 0) := by
  by_cases hv : v ∈ rows c
  · have hf : ((Finset.range n).erase v).filter (fun w => w ∈ rows c) =
        (rows c).erase v := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨hne, _⟩, hm⟩
        exact ⟨hne, hm⟩
      · rintro ⟨hne, hm⟩
        exact ⟨⟨hne, hbound hm⟩, hm⟩
    simp only [hv, true_and, ite_true, mul_one, Finset.sum_boole]
    rw [hf, Finset.card_erase_of_mem hv, hcard]
    simp
  · simp [hv]

/-- Uniform double counting, with no fixed number of vertices or row size. -/
theorem double_count (n k : Nat) (rows : Nat → Finset Nat) (v : Nat)
    (hcard : ∀ c, c < n → (rows c).card = k)
    (hbound : ∀ c, c < n → rows c ⊆ Finset.range n) :
    (k - 1) * (incomingCenters n rows v).card =
      ∑ w ∈ (Finset.range n).erase v, (pairCenters n rows v w).card := by
  calc
    (k - 1) * (incomingCenters n rows v).card =
        ∑ c ∈ Finset.range n, (k - 1) * (if v ∈ rows c then 1 else 0) := by
      rw [← Finset.mul_sum]
      simp [incomingCenters, Finset.sum_boole]
    _ = ∑ c ∈ Finset.range n, ∑ w ∈ (Finset.range n).erase v,
        if v ∈ rows c ∧ w ∈ rows c then (1 : Nat) else 0 := by
      apply Finset.sum_congr rfl
      intro c hc
      exact (local_partners n k rows c v
        (hcard c (Finset.mem_range.mp hc)) (hbound c (Finset.mem_range.mp hc))).symm
    _ = ∑ w ∈ (Finset.range n).erase v, ∑ c ∈ Finset.range n,
        if v ∈ rows c ∧ w ∈ rows c then (1 : Nat) else 0 := Finset.sum_comm
    _ = ∑ w ∈ (Finset.range n).erase v, (pairCenters n rows v w).card := by
      simp [pairCenters, Finset.sum_boole]

/-- Pair incidence constraints imply a uniform bound for all n,k,lambda. -/
theorem incoming_budget (n k lam : Nat) (rows : Nat → Finset Nat) (v : Nat)
    (hv : v < n)
    (hcard : ∀ c, c < n → (rows c).card = k)
    (hbound : ∀ c, c < n → rows c ⊆ Finset.range n)
    (hpair : ∀ w, w < n → v ≠ w → (pairCenters n rows v w).card ≤ lam) :
    (k - 1) * (incomingCenters n rows v).card ≤ (n - 1) * lam := by
  rw [double_count n k rows v hcard hbound]
  calc
    _ ≤ ∑ _w ∈ (Finset.range n).erase v, lam := by
      apply Finset.sum_le_sum
      intro w hw
      obtain ⟨hwv, hw⟩ := Finset.mem_erase.mp hw
      exact hpair w (Finset.mem_range.mp hw) hwv.symm
    _ = (n - 1) * lam := by
      simp [Finset.card_erase_of_mem (Finset.mem_range.mpr hv)]

/-- The historical six-bound is a corollary, not a universal constant. -/
theorem eleven_four_incoming_le_six (rows : Nat → Finset Nat) (v : Nat)
    (hv : v < 11)
    (hcard : ∀ c, c < 11 → (rows c).card = 4)
    (hbound : ∀ c, c < 11 → rows c ⊆ Finset.range 11)
    (hpair : ∀ w, w < 11 → v ≠ w → (pairCenters 11 rows v w).card ≤ 2) :
    (incomingCenters 11 rows v).card ≤ 6 := by
  have h := incoming_budget 11 4 2 rows v hv hcard hbound hpair
  omega

end E97Structural37

#print axioms E97Structural37.double_count
#print axioms E97Structural37.incoming_budget
#print axioms E97Structural37.eleven_four_incoming_le_six
