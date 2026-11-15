import BlockB_EuclideanGeometry_CANDIDATE

/-!
E97 V12 geometric bridge, stage 1: prove the genuinely STRICT Euclidean
triangle inequality directly from a nonzero XY orientation. This is not
an abstract positivity hypothesis and depends on no unproved K/F certificate.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97Geo12
open E97BlockB

noncomputable def xyLen (a b : XY) : ℝ := Real.sqrt (sqDist a b)

theorem sqDist_nonneg (a b : XY) : 0 ≤ sqDist a b := by
  dsimp [sqDist]
  positivity

theorem xyLen_nonneg (a b : XY) : 0 ≤ xyLen a b := by
  exact Real.sqrt_nonneg _

theorem xyLen_sq (a b : XY) : (xyLen a b)^2 = sqDist a b := by
  exact Real.sq_sqrt (sqDist_nonneg a b)

theorem xyLen_symm (a b : XY) : xyLen a b = xyLen b a := by
  unfold xyLen
  congr 1
  dsimp [sqDist]
  ring

/-- Scalar product of the successive vectors b-a and c-b. -/
def turnDot (a b c : XY) : ℝ :=
  (b.1-a.1)*(c.1-b.1) + (b.2-a.2)*(c.2-b.2)

theorem chord_sq_identity (a b c : XY) :
    sqDist a c = sqDist a b + sqDist b c + 2 * turnDot a b c := by
  dsimp [sqDist, turnDot]
  ring

theorem turn_gram_identity (a b c : XY) :
    (turnDot a b c)^2 + (orient a b c)^2 =
      sqDist a b * sqDist b c := by
  dsimp [sqDist, turnDot, orient]
  ring

/-- Determinant nonzero implies a strict (not weak) Euclidean triangle
inequality for the actual sqrt-of-squared-distance model used in V10. -/
theorem strict_triangle_of_nonnezero_orient (a b c : XY)
    (hor : orient a b c ≠ 0) :
    xyLen a c < xyLen a b + xyLen b c := by
  let u : ℝ := xyLen a b
  let v : ℝ := xyLen b c
  let w : ℝ := xyLen a c
  have hu : 0 ≤ u := xyLen_nonneg a b
  have hv : 0 ≤ v := xyLen_nonneg b c
  have hw : 0 ≤ w := xyLen_nonneg a c
  have hu2 : u^2 = sqDist a b := xyLen_sq a b
  have hv2 : v^2 = sqDist b c := xyLen_sq b c
  have hw2 : w^2 = sqDist a c := xyLen_sq a c
  have hgram : (turnDot a b c)^2 + (orient a b c)^2 = (u*v)^2 := by
    calc
      _ = sqDist a b * sqDist b c := turn_gram_identity a b c
      _ = (u*v)^2 := by rw [← hu2, ← hv2]; ring
  have hpositive : 0 < (orient a b c)^2 := sq_pos_of_ne_zero hor
  have hdot : turnDot a b c < u*v := by
    by_contra hnot
    have hge : u*v ≤ turnDot a b c := le_of_not_gt hnot
    have huv : 0 ≤ u*v := mul_nonneg hu hv
    have hdn : 0 ≤ turnDot a b c := le_trans huv hge
    have hmul : 0 ≤ (turnDot a b c - u*v) *
        (turnDot a b c + u*v) :=
      mul_nonneg (sub_nonneg.mpr hge) (add_nonneg hdn huv)
    nlinarith
  have hchord : w^2 = u^2 + v^2 + 2*turnDot a b c := by
    rw [hw2, hu2, hv2]
    exact chord_sq_identity a b c
  have hstrict : w^2 < (u+v)^2 := by nlinarith
  nlinarith

#print axioms E97Geo12.sqDist_nonneg
#print axioms E97Geo12.xyLen_nonneg
#print axioms E97Geo12.xyLen_sq
#print axioms E97Geo12.xyLen_symm
#print axioms E97Geo12.chord_sq_identity
#print axioms E97Geo12.turn_gram_identity
#print axioms E97Geo12.strict_triangle_of_nonnezero_orient
end E97Geo12
