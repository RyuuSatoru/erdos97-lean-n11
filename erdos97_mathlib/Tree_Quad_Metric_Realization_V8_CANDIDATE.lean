import Tree_KF_PositiveMetric_V6_CANDIDATE

/-!
Erdos #97 — V8: bridge the actual `getQuad` four-edge differences to
`projectedValue` of the 55-dimensional reduced coefficient vector.

Explicit trust boundary: coherence of the union-find representatives with
real edge lengths and positivity of the actual quadrilateral gap still
require geometric proofs from StrictCCW11 and realized selected rows.
No new axioms, no sorry, and no claim that the full tree was checked by Lean.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97TreeMetricV8
open E97TreeKF4 E97TreeMetricV6

/-- Representative stored by the exact V4 certificate class array. -/
def classRep (classes : Array Nat) (edge : Nat) : Nat :=
  (classes[edge]?).getD edge

/-- The real geometric length assigned to edge e agrees with the metric of
its class representative. This is the exact unproved row-realization bridge. -/
def CoherentClasses (classes : Array Nat) (trueLength : Nat → ℝ) : Prop :=
  ∀ e, e < 55 → trueLength e = trueLength (classRep classes e)

/-- The literal 4-edge expression from the canonical `E97Flow.getQuad`. -/
def actualQuadGap (trueLength : Nat → ℝ) (q : Nat) : ℝ :=
  let (a,b,c,d) := E97Flow.getQuad q
  trueLength a + trueLength b - trueLength c - trueLength d

/-- The same quadrilateral evaluated on representative-class lengths. -/
def reducedQuadGap (classes : Array Nat) (classLength : Nat → ℝ)
    (q : Nat) : ℝ :=
  let (a,b,c,d) := E97Flow.getQuad q
  classLength (classRep classes a) + classLength (classRep classes b) -
    classLength (classRep classes c) - classLength (classRep classes d)

/-- Finitely check the real 660-quadrilateral table: all four edges
are among the 55 actual unordered edges. Kernel checks actual getQuad. -/
theorem all_actual_quad_edges_bounded :
    (List.range 660).all (fun q =>
      let (a,b,c,d) := E97Flow.getQuad q
      decide (a < 55 ∧ b < 55 ∧ c < 55 ∧ d < 55)) = true := by
  decide +kernel

/-- Every actual quadrilateral has four in-range edges. -/
theorem quad_edges_bounded (q : Nat) (hq : q < 660) :
    let (a,b,c,d) := E97Flow.getQuad q
    a < 55 ∧ b < 55 ∧ c < 55 ∧ d < 55 := by
  have h := (List.all_eq_true.mp all_actual_quad_edges_bounded)
    q (List.mem_range.mpr hq)
  simpa only [decide_eq_true_eq] using h

/-- All representative IDs in the real first F certificate are legal. -/
theorem firstF_representatives_bounded :
    (List.range 55).all (fun e =>
      decide (classRep firstFClasses e < 55)) = true := by
  decide +kernel

/-- A one-hot coefficient in the finite 55-coordinate basis evaluates
exactly to the chosen representative's real edge length. -/
private theorem one_hot (length : Nat → ℝ) (r : Nat) (hr : r < 55) :
    (∑ e ∈ Finset.range 55,
      (((if r == e then (1 : Int) else 0) : Int) : ℝ) * length e) =
      length r := by
  classical
  simp [beq_iff_eq, hr]

/-- A reduced coefficient vector evaluates to the corresponding genuine
four-edge expression on representative-class lengths. -/
theorem projected_eq_reduced_quad (classes : Array Nat)
    (classLength : Nat → ℝ) (q : Nat)
    (hrep : ∀ e, e < 55 → classRep classes e < 55)
    (hq : q < 660) :
    projectedValue classes classLength q =
      reducedQuadGap classes classLength q := by
  have hbound := quad_edges_bounded q hq
  rcases hquad : E97Flow.getQuad q with ⟨a,b,c,d⟩
  simp only [hquad] at hbound
  have ha : classRep classes a < 55 := hrep a hbound.1
  have hb : classRep classes b < 55 := hrep b hbound.2.1
  have hc : classRep classes c < 55 := hrep c hbound.2.2.1
  have hd : classRep classes d < 55 := hrep d hbound.2.2.2
  simp only [projectedValue, reducedCoeff, reducedQuadGap, classRep, hquad,
    Int.cast_sub, Int.cast_add, add_mul, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- The preceding simp unfolded classRep, so supply the literal
  -- Array.getD representatives that occur in the reduced coefficients.
  have haRaw : (classes[a]?).getD a < 55 := by
    simpa only [classRep] using ha
  have hbRaw : (classes[b]?).getD b < 55 := by
    simpa only [classRep] using hb
  have hcRaw : (classes[c]?).getD c < 55 := by
    simpa only [classRep] using hc
  have hdRaw : (classes[d]?).getD d < 55 := by
    simpa only [classRep] using hd
  rw [one_hot classLength ((classes[a]?).getD a) haRaw,
      one_hot classLength ((classes[b]?).getD b) hbRaw,
      one_hot classLength ((classes[c]?).getD c) hcRaw,
      one_hot classLength ((classes[d]?).getD d) hdRaw]

/-- A coherent class metric converts the reduced expression into the
actual quadrilateral gap of four source edges. -/
theorem reduced_quad_eq_actual (classes : Array Nat)
    (trueLength : Nat → ℝ) (q : Nat)
    (hcoherent : CoherentClasses classes trueLength) (hq : q < 660) :
    reducedQuadGap classes trueLength q = actualQuadGap trueLength q := by
  have hbound := quad_edges_bounded q hq
  rcases hquad : E97Flow.getQuad q with ⟨a,b,c,d⟩
  simp only [hquad] at hbound
  have ha := hcoherent a hbound.1
  have hb := hcoherent b hbound.2.1
  have hc := hcoherent c hbound.2.2.1
  have hd := hcoherent d hbound.2.2.2
  simp only [reducedQuadGap, actualQuadGap, hquad]
  rw [ha, hb, hc, hd]

/-- The main metric bridge. Under faithfully realized row equalities,
the quadrilateral scalar in v7 is the literal four-edge metric gap. -/
theorem projected_eq_actual_quad (classes : Array Nat)
    (trueLength : Nat → ℝ) (q : Nat)
    (hrep : ∀ e, e < 55 → classRep classes e < 55)
    (hcoherent : CoherentClasses classes trueLength) (hq : q < 660) :
    projectedValue classes trueLength q = actualQuadGap trueLength q := by
  rw [projected_eq_reduced_quad classes trueLength q hrep hq]
  exact reduced_quad_eq_actual classes trueLength q hcoherent hq

/-- An actually positive quadrilateral gap becomes a positive V7
projected coefficient valuation under coherent equal-edge classes. -/
theorem positive_projected_of_actual_gap (classes : Array Nat)
    (trueLength : Nat → ℝ) (q : Nat)
    (hrep : ∀ e, e < 55 → classRep classes e < 55)
    (hcoherent : CoherentClasses classes trueLength)
    (hq : q < 660) (hpositive : 0 < actualQuadGap trueLength q) :
    0 < projectedValue classes trueLength q := by
  rw [projected_eq_actual_quad classes trueLength q hrep hcoherent hq]
  exact hpositive

/-- The first REAL F witness cannot coexist with coherent edge classes and
three positive actual quadrilateral inequalities. Notice that the two
geometric hypotheses remain explicit; this is NOT StrictCCW11 -> positivity. -/
theorem first_F_impossible_of_actual_metric (trueLength : Nat → ℝ)
    (hcoherent : CoherentClasses firstFClasses trueLength)
    (h14 : 0 < actualQuadGap trueLength 14)
    (h288 : 0 < actualQuadGap trueLength 288)
    (h655 : 0 < actualQuadGap trueLength 655) : False := by
  have hrep : ∀ e, e < 55 → classRep firstFClasses e < 55 := by
    intro e he
    have hp := (List.all_eq_true.mp firstF_representatives_bounded)
      e (List.mem_range.mpr he)
    exact decide_eq_true_eq.mp hp
  exact first_real_F_contradicts_positive_metric trueLength
    (positive_projected_of_actual_gap firstFClasses trueLength 14
      hrep hcoherent (by omega) h14)
    (positive_projected_of_actual_gap firstFClasses trueLength 288
      hrep hcoherent (by omega) h288)
    (positive_projected_of_actual_gap firstFClasses trueLength 655
      hrep hcoherent (by omega) h655)

#print axioms E97TreeMetricV8.all_actual_quad_edges_bounded
#print axioms E97TreeMetricV8.quad_edges_bounded
#print axioms E97TreeMetricV8.firstF_representatives_bounded
#print axioms E97TreeMetricV8.projected_eq_reduced_quad
#print axioms E97TreeMetricV8.reduced_quad_eq_actual
#print axioms E97TreeMetricV8.projected_eq_actual_quad
#print axioms E97TreeMetricV8.positive_projected_of_actual_gap
#print axioms E97TreeMetricV8.first_F_impossible_of_actual_metric
end E97TreeMetricV8
