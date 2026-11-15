import A2_ActualRows_CANDIDATE
import Mathlib

/-!
Erdős #97, A2: selected-prefix counting semantics, not just an abstract
counting bound. All row membership tests below use the already kernel-checked
`E97A2Rows.decodedWitnesses` of the actual `E97Flow.getRow` table.

This module does not claim that the entire tree parser is sound. It checks
that the numerical counters can be interpreted as the number of rows in a
specific selected path, and that adding a row increments exactly the relevant
counter. It also connects the Boolean path-range check to the proven table.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace E97A2Prefix
open E97A2Rows E97Flow

/-- The four (decoded) witness vertex IDs in the actual `getRow p` row. -/
def rowWitnessSet (p : Nat) : Finset Nat :=
  let (a, b, c, d) := decodedWitnesses p
  {a, b, c, d}

/-- Increment for a witness vertex in a selected row. -/
def vertexHit (p v : Nat) : Nat :=
  if v ∈ rowWitnessSet p then 1 else 0

/-- Increment for an unordered witness pair in a selected row. -/
def pairHit (p u v : Nat) : Nat :=
  if u ∈ rowWitnessSet p ∧ v ∈ rowWitnessSet p then 1 else 0

/-- The actual A2 incoming counter recomputed from the selected row list. -/
def incomingCount (path : List Nat) (v : Nat) : Nat :=
  (path.map (fun p => vertexHit p v)).sum

/-- The actual A2 pair counter recomputed from the selected row list. -/
def pairCount (path : List Nat) (u v : Nat) : Nat :=
  (path.map (fun p => pairHit p u v)).sum

@[simp] theorem incoming_cons (p : Nat) (path : List Nat) (v : Nat) :
    incomingCount (p :: path) v = vertexHit p v + incomingCount path v := by
  simp [incomingCount]

@[simp] theorem pair_cons (p : Nat) (path : List Nat) (u v : Nat) :
    pairCount (p :: path) u v = pairHit p u v + pairCount path u v := by
  simp [pairCount]

/-- Incoming counts are exactly the number of selected rows containing v. -/
theorem incoming_eq_filter_length (path : List Nat) (v : Nat) :
    incomingCount path v =
    (path.filter (fun p => v ∈ rowWitnessSet p)).length := by
  induction path with
  | nil => simp [incomingCount]
  | cons p ps ih =>
      by_cases h : v ∈ rowWitnessSet p
      · simp [vertexHit, h, ih]; omega
      · simp [vertexHit, h, ih]

/-- Pair counts are exactly the number of selected rows containing u and v. -/
theorem pair_eq_filter_length (path : List Nat) (u v : Nat) :
    pairCount path u v =
    (path.filter (fun p => u ∈ rowWitnessSet p ∧ v ∈ rowWitnessSet p)).length := by
  induction path with
  | nil => simp [pairCount]
  | cons p ps ih =>
      by_cases h : u ∈ rowWitnessSet p ∧ v ∈ rowWitnessSet p
      · simp [pairHit, h, ih]; omega
      · simp [pairHit, h, ih]

/-- Selecting one additional row updates the vertex counter exactly once. -/
theorem incoming_append_row (path : List Nat) (p v : Nat) :
    incomingCount (path ++ [p]) v = incomingCount path v + vertexHit p v := by
  simp [incomingCount]

/-- Selecting one additional row updates the pair counter exactly once. -/
theorem pair_append_row (path : List Nat) (p u v : Nat) :
    pairCount (path ++ [p]) u v = pairCount path u v + pairHit p u v := by
  simp [pairCount]

/-- The real selected-prefix incoming counter disallows a seventh hit. -/
theorem reject_seventh_selected_row
    (path : List Nat) (p v : Nat)
    (hmem : v ∈ rowWitnessSet p)
    (hseen : 6 ≤ incomingCount path v)
    (hlegal : incomingCount (path ++ [p]) v ≤ 6) : False := by
  rw [incoming_append_row] at hlegal
  simp [vertexHit, hmem] at hlegal
  omega

/-- The real selected-prefix pair counter disallows a third hit. -/
theorem reject_third_selected_pair
    (path : List Nat) (p u v : Nat)
    (hmem : u ∈ rowWitnessSet p ∧ v ∈ rowWitnessSet p)
    (hseen : 2 ≤ pairCount path u v)
    (hlegal : pairCount (path ++ [p]) u v ≤ 2) : False := by
  rw [pair_append_row] at hlegal
  simp [pairHit, hmem] at hlegal
  omega

/-- Extract a valid row from the already kernel-proved finite table scan. -/
theorem actual_row_ok_of_lt (p : Nat) (hp : p < 2310) :
    actualRowOK p = true := by
  exact (List.all_eq_true.mp all_actual_rows_valid) p (List.mem_range.mpr hp)

/-- Every in-range selected prefix uses actual (well-formed) `getRow` rows. -/
theorem actual_rows_of_checked_path
    (path : List Nat)
    (hpath : path.all (fun p => decide (p < 2310)) = true)
    (p : Nat) (hp : p ∈ path) : actualRowOK p = true := by
  have hchecked : decide (p < 2310) = true :=
    (List.all_eq_true.mp hpath) p hp
  have hbound : p < 2310 := by
    simpa only [decide_eq_true_eq] using hchecked
  exact actual_row_ok_of_lt p hbound

/-- A sound `validFlow` leaf invokes only genuine in-range rows of the
    previously kernel-verified `getRow` table. This does NOT verify the tree. -/
theorem actual_rows_of_validFlow
    (path : List Nat) (weighted : List WeightedQuad) (eqs : List EqWitness)
    (hflow : validFlow path weighted eqs = true)
    (p : Nat) (hp : p ∈ path) : actualRowOK p = true := by
  have hpath : path.all (fun p => decide (p < 2310)) = true := by
    unfold validFlow at hflow
    simp only [Bool.and_eq_true] at hflow
    tauto
  exact actual_rows_of_checked_path path hpath p hp

#print axioms E97A2Prefix.incoming_eq_filter_length
#print axioms E97A2Prefix.pair_eq_filter_length
#print axioms E97A2Prefix.incoming_append_row
#print axioms E97A2Prefix.pair_append_row
#print axioms E97A2Prefix.reject_seventh_selected_row
#print axioms E97A2Prefix.reject_third_selected_pair
#print axioms E97A2Prefix.actual_row_ok_of_lt
#print axioms E97A2Prefix.actual_rows_of_checked_path
#print axioms E97A2Prefix.actual_rows_of_validFlow
end E97A2Prefix
