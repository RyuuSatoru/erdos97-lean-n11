import Thin_Checker_V29

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace E97Structural37
open T29E97EdgeWalk22

/-- A walk proved from a small set of rows stays valid in every larger context. -/
theorem checkWalk_mono (small big : List Nat)
    (hsub : ∀ r ∈ small, r ∈ big) (start finish : Nat)
    (steps : List (Nat × Nat))
    (h : checkWalk small start finish steps = true) :
    checkWalk big start finish steps = true := by
  induction steps generalizing start with
  | nil => simpa only [checkWalk] using h
  | cons step rest ih =>
    rcases step with ⟨row, next⟩
    simp only [checkWalk, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨⟨⟨hsub row h.1.1.1, h.1.1.2⟩, h.1.2⟩, ih next h.2⟩

theorem checkPairings_mono (small big : List Nat)
    (hsub : ∀ r ∈ small, r ∈ big) (starts : List Nat) (receipts : List Receipt)
    (h : checkPairings small starts receipts = true) :
    checkPairings big starts receipts = true := by
  induction starts generalizing receipts with
  | nil => cases receipts <;> simp_all [checkPairings]
  | cons e es ih =>
    cases receipts with
    | nil => simp [checkPairings] at h
    | cons receipt rest =>
      rcases receipt with ⟨finish, steps⟩
      simp only [checkPairings, Bool.and_eq_true] at h ⊢
      exact ⟨checkWalk_mono small big hsub e finish steps h.1, ih rest h.2⟩

/-- One checked obstruction can close every context containing its supporting rows.
This does not assert that the obstruction supports cover the entire search space. -/
theorem checkedFlow_mono (small big : List Nat)
    (hsub : ∀ r ∈ small, r ∈ big)
    (terms : List (Nat × Nat)) (receipts : List Receipt)
    (h : checkedFlow small terms receipts = true) :
    checkedFlow big terms receipts = true := by
  simp only [checkedFlow, Bool.and_eq_true] at h ⊢
  exact ⟨⟨h.1.1, checkPairings_mono small big hsub _ receipts h.1.2⟩, h.2⟩

end E97Structural37

#print axioms E97Structural37.checkWalk_mono
#print axioms E97Structural37.checkPairings_mono
#print axioms E97Structural37.checkedFlow_mono
