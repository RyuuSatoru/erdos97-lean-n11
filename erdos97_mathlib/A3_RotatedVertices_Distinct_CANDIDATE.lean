import A3_PatternAt_Decode_CANDIDATE
/-! All five indices from a rotated five-subset are distinct and < 11.
The finite five-subset validity theorem is the ONLY combinatorial input. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
-- Equivalent goalwise tactic structure avoids unused <;> warnings.
-- `-DwarningAsError=true` and explicit #print axioms audits remain enabled.
set_option linter.unnecessarySeqFocus false
namespace E97A3Pattern
open E97A3Index

/-- Exactly the index bounds and distinctness conditions required for
both BC and AB real-row A3 soundness theorems. -/
theorem rotated_vertices_valid (i t : Nat) (hi : i < 462) (ht : t < 5) :
    let p := rot5 i t 0
    let a := rot5 i t 1
    let b := rot5 i t 2
    let c := rot5 i t 3
    let q := rot5 i t 4
    p < 11 ∧ a < 11 ∧ b < 11 ∧ c < 11 ∧ q < 11 ∧
    p ≠ a ∧ q ≠ a ∧ q ≠ b ∧ a ≠ b ∧
    p ≠ b ∧ p ≠ c ∧ b ≠ c ∧ q ≠ c := by
  obtain ⟨h01, h12, h23, h34, h4⟩ := five_valid_of_lt i hi
  interval_cases t
  all_goals simp [rot5]
  all_goals omega

/-- Index-validity of every A3 reason code, without assuming separate
vertex bounds or distinctness of the payload. -/
theorem code_vertices_valid (code : Nat)
    (hlo : 55 < code) (hhi : code ≤ 4675) :
    let i := (code - 56) / 10
    let t := ((code - 56) % 10) / 2
    let p := rot5 i t 0
    let a := rot5 i t 1
    let b := rot5 i t 2
    let c := rot5 i t 3
    let q := rot5 i t 4
    p < 11 ∧ a < 11 ∧ b < 11 ∧ c < 11 ∧ q < 11 ∧
    p ≠ a ∧ q ≠ a ∧ q ≠ b ∧ a ≠ b ∧
    p ≠ b ∧ p ≠ c ∧ b ≠ c ∧ q ≠ c := by
  have hi : (code - 56) / 10 < 462 := by omega
  have ht : ((code - 56) % 10) / 2 < 5 := by omega
  exact rotated_vertices_valid _ _ hi ht

#print axioms E97A3Pattern.rotated_vertices_valid
#print axioms E97A3Pattern.code_vertices_valid
end E97A3Pattern
