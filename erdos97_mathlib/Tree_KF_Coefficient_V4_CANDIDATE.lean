import FlowCheckCore

/-!
Tree protocol v4: kernel-readable, concrete K2 and F coefficient obligations
on two exact records from the canonical E97TREE 4 11 2 tree.
The selected rows are looked up through the real E97Flow.getRow table.
This does not certify the transcript's B traversal, global tree completeness,
or the geometric metric realization of the projected coefficient values.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97TreeKF4

/-- Canonical representatives for 55 edge variables before row equalities. -/
def emptyClasses : Array Nat := (List.range 55).toArray

/-- Union two current equality classes. Replaces all members of the larger
class by the smaller representative, including after earlier unions. -/
def mergeClasses (classes : Array Nat) (edge1 edge2 : Nat) : Array Nat :=
  let r1 := (classes[edge1]?).getD edge1
  let r2 := (classes[edge2]?).getD edge2
  classes.map (fun r => if r == max r1 r2 then min r1 r2 else r)

/-- A selected true row identifies its four spoke edge variables. -/
def addActualRow (classes : Array Nat) (rowId : Nat) : Array Nat :=
  let (a,b,c,d) := E97Flow.getRow rowId
  mergeClasses (mergeClasses (mergeClasses classes a b) a c) a d

/-- The canonical first K occurs after B0(row 0), B10(row 64), B9(row 133). -/
def firstKClasses : Array Nat :=
  addActualRow (addActualRow (addActualRow emptyClasses 0) 2164) 2023

/-- The first F occurs with B0(row 1), B1(row 24), B9(row 209), B10(row 126). -/
def firstFClasses : Array Nat :=
  addActualRow (addActualRow (addActualRow (addActualRow emptyClasses 1) 234) 2099) 2226

/-- Coefficient of a representative in one ACTUAL quadrilateral from getQuad. -/
def reducedCoeff (classes : Array Nat) (q representative : Nat) : Int :=
  let (a,b,c,d) := E97Flow.getQuad q
  (if (classes[a]?).getD a == representative then (1 : Int) else 0) +
  (if (classes[b]?).getD b == representative then (1 : Int) else 0) -
  (if (classes[c]?).getD c == representative then (1 : Int) else 0) -
  (if (classes[d]?).getD d == representative then (1 : Int) else 0)

/-- K2 requires component-wise opposite coefficient vectors and nonzero first
vector. (No use of native_decide or external arithmetic oracles.) -/
def checkedK2 (classes : Array Nat) (q r : Nat) : Bool :=
  decide (q < 660 ∧ r < 660) &&
  (List.range 55).all (fun e => decide
      (reducedCoeff classes q e + reducedCoeff classes r e = 0)) &&
  (List.range 55).any (fun e => decide (reducedCoeff classes q e ≠ 0))

/-- K0 requires that all 55 coordinates of a quadrilateral vector vanish. -/
def checkedK0 (classes : Array Nat) (q : Nat) : Bool :=
  decide (q < 660) &&
  (List.range 55).all (fun e => decide (reducedCoeff classes q e = 0))

/-- F checks positive integer weights, legal quad IDs and zero vector. -/
def checkedF (classes : Array Nat) (terms : List (Nat × Nat)) : Bool :=
  (!terms.isEmpty) &&
  terms.all (fun qw => decide (qw.1 < 660 ∧ 0 < qw.2 ∧ qw.2 ≤ 1000000)) &&
  (List.range 55).all (fun e => decide
    ((terms.foldl (fun acc qw => acc + (Int.ofNat qw.2) *
      reducedCoeff classes qw.1 e) (0 : Int)) = 0))

/-- A passing K2 checker certifies coefficient cancellation for EVERY root. -/
theorem checkedK2_coeff_balance (classes : Array Nat) (q r e : Nat)
    (h : checkedK2 classes q r = true) (he : e < 55) :
    reducedCoeff classes q e + reducedCoeff classes r e = 0 := by
  have hscan : (List.range 55).all (fun j => decide
      (reducedCoeff classes q j + reducedCoeff classes r j = 0)) = true :=
    by
      have hs := h
      simp only [checkedK2, Bool.and_eq_true] at hs
      exact hs.1.2
  exact decide_eq_true_eq.mp ((List.all_eq_true.mp hscan) e (List.mem_range.mpr he))

/-- A passing F checker certifies the exact integer coefficient balance. -/
theorem checkedF_coeff_balance (classes : Array Nat)
    (terms : List (Nat × Nat)) (e : Nat)
    (h : checkedF classes terms = true) (he : e < 55) :
    terms.foldl (fun acc qw => acc + (Int.ofNat qw.2) *
      reducedCoeff classes qw.1 e) (0 : Int) = 0 := by
  have hscan : (List.range 55).all (fun j => decide
    ((terms.foldl (fun acc qw => acc + (Int.ofNat qw.2) *
      reducedCoeff classes qw.1 j) (0 : Int)) = 0)) = true :=
    by
      have hs := h
      simp only [checkedF, Bool.and_eq_true] at hs
      exact hs.2
  exact decide_eq_true_eq.mp ((List.all_eq_true.mp hscan) e (List.mem_range.mpr he))

/-- Linear valuation of the reduced coefficient vector over real edge lengths. -/
def projectedValue (classes : Array Nat) (edgeLength : Nat → ℝ) (q : Nat) : ℝ :=
  ∑ e ∈ Finset.range 55, (reducedCoeff classes q e : ℝ) * edgeLength e

/-- K2 coefficient cancellation implies the sum of the two linear valuations
is EXACTLY zero. This bridges boolean integer checks to real arithmetic. -/
theorem checkedK2_projected_sum_zero (classes : Array Nat)
    (edgeLength : Nat → ℝ) (q r : Nat)
    (h : checkedK2 classes q r = true) :
    projectedValue classes edgeLength q + projectedValue classes edgeLength r = 0 := by
  unfold projectedValue
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro e he
  have hc : reducedCoeff classes q e + reducedCoeff classes r e = 0 :=
    checkedK2_coeff_balance classes q r e h (Finset.mem_range.mp he)
  calc
    (reducedCoeff classes q e : ℝ) * edgeLength e +
      (reducedCoeff classes r e : ℝ) * edgeLength e =
        ((reducedCoeff classes q e : ℝ) +
         (reducedCoeff classes r e : ℝ)) * edgeLength e := by ring
    _ = 0 := by
      have hreal : (reducedCoeff classes q e : ℝ) +
          (reducedCoeff classes r e : ℝ) = 0 := by exact_mod_cast hc
      rw [hreal]
      simp

/-- A K2 certificate cannot coexist with strict positivity of both
projected quadrilateral evaluations. Geometry->positivity remains a separate
bridge obligation; not assumed as a new primitive in this module. -/
theorem positive_projected_K2_impossible (classes : Array Nat)
    (edgeLength : Nat → ℝ) (q r : Nat)
    (h : checkedK2 classes q r = true)
    (hq : 0 < projectedValue classes edgeLength q)
    (hr : 0 < projectedValue classes edgeLength r) : False := by
  have hz := checkedK2_projected_sum_zero classes edgeLength q r h
  linarith

/-- Real source rows referenced by the two concrete witness prefixes. -/
theorem firstK_actual_source_rows :
    E97Flow.getRow 0 = (0,1,2,3) ∧
    E97Flow.getRow 2164 = (9,39,44,48) ∧
    E97Flow.getRow 2023 = (17,43,50,52) := by
  decide +kernel

/-- The first K 609 38 is valid under classes computed from actual getRow. -/
theorem first_real_K2_pass : checkedK2 firstKClasses 609 38 = true := by
  decide +kernel

/-- A modified K 608 38 must be rejected by the SAME kernel checker. -/
theorem forged_real_K2_rejected : checkedK2 firstKClasses 608 38 = false := by
  decide +kernel

/-- The first actual F is at record 6901: F 3 14 1 288 1 655 1. -/
theorem first_real_F_pass :
    checkedF firstFClasses [(14,1),(288,1),(655,1)] = true := by
  decide +kernel

/-- Replacing quad 655 by 654 invalidates the real F certificate. -/
theorem forged_real_F_rejected :
    checkedF firstFClasses [(14,1),(288,1),(654,1)] = false := by
  decide +kernel

#print axioms E97TreeKF4.checkedK2_coeff_balance
#print axioms E97TreeKF4.checkedF_coeff_balance
#print axioms E97TreeKF4.checkedK2_projected_sum_zero
#print axioms E97TreeKF4.positive_projected_K2_impossible
#print axioms E97TreeKF4.firstK_actual_source_rows
#print axioms E97TreeKF4.first_real_K2_pass
#print axioms E97TreeKF4.forged_real_K2_rejected
#print axioms E97TreeKF4.first_real_F_pass
#print axioms E97TreeKF4.forged_real_F_rejected
end E97TreeKF4
