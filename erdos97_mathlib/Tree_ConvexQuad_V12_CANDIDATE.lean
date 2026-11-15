import Tree_StrictTriangle_V12_CANDIDATE

/-!
E97 V12 geometric bridge, stage 2. The two diagonals of a strict CCW
quadrilateral intersect in their interiors. Four STRICT triangle inequalities
at that actual point imply both diagonals > opposite sides inequalities.
No hypothesis about `actualQuadGap` or `projectedValue` occurs here.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97ConvexQuad12
open E97BlockB E97Geo12

def onChord (a c : XY) (t : ℝ) : XY :=
  (a.1 + t*(c.1-a.1), a.2 + t*(c.2-a.2))

theorem sqDist_onChord_left (a c : XY) (t : ℝ) :
    sqDist a (onChord a c t) = t^2 * sqDist a c := by
  dsimp [sqDist, onChord]
  ring

theorem sqDist_onChord_right (a c : XY) (t : ℝ) :
    sqDist (onChord a c t) c = (1-t)^2 * sqDist a c := by
  dsimp [sqDist, onChord]
  ring

theorem xyLen_onChord_left (a c : XY) (t : ℝ) (ht : 0 ≤ t) :
    xyLen a (onChord a c t) = t * xyLen a c := by
  have h1 := xyLen_sq a (onChord a c t)
  have h2 := xyLen_sq a c
  rw [sqDist_onChord_left, ← h2] at h1
  have hl := xyLen_nonneg a (onChord a c t)
  have hr := mul_nonneg ht (xyLen_nonneg a c)
  nlinarith [sq_nonneg (xyLen a (onChord a c t) + t * xyLen a c)]

theorem xyLen_onChord_right (a c : XY) (t : ℝ) (ht : t ≤ 1) :
    xyLen (onChord a c t) c = (1-t) * xyLen a c := by
  have h1 := xyLen_sq (onChord a c t) c
  have h2 := xyLen_sq a c
  rw [sqDist_onChord_right, ← h2] at h1
  have hl := xyLen_nonneg (onChord a c t) c
  have hr := mul_nonneg (sub_nonneg.mpr ht) (xyLen_nonneg a c)
  nlinarith [sq_nonneg (xyLen (onChord a c t) c + (1-t) * xyLen a c)]

theorem xyLen_onChord_add (a c : XY) (t : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    xyLen a (onChord a c t) + xyLen (onChord a c t) c =
      xyLen a c := by
  rw [xyLen_onChord_left a c t ht, xyLen_onChord_right a c t ht1]
  ring

/-- Equal Cartesian coordinates, using the exact crossing numerator
identities already proved in the 2017-style Block B kernel. -/
theorem two_diagonals_meet (a b c d : XY)
    (hD : 0 < diagDelta a b c d) :
    onChord a c (diagT a b c d / diagDelta a b c d) =
      onChord b d (diagS a b c d / diagDelta a b c d) := by
  apply Prod.ext
  · dsimp [onChord]
    have hx := E97BlockB.diagonal_cross_x a b c d
    have hne : diagDelta a b c d ≠ 0 := ne_of_gt hD
    field_simp
    nlinarith
  · dsimp [onChord]
    have hy := E97BlockB.diagonal_cross_y a b c d
    have hne : diagDelta a b c d ≠ 0 := ne_of_gt hD
    field_simp
    nlinarith

/-- Generic convex quadrilateral inequality for the actual Cartesian
Euclidean sqrt metric, proved from only four positive orientations. -/
theorem convex_quad_strict (a b c d : XY)
    (habc : 0 < orient a b c)
    (habd : 0 < orient a b d)
    (hbcd : 0 < orient b c d)
    (hacd : 0 < orient a c d) :
    xyLen a b + xyLen c d < xyLen a c + xyLen b d ∧
    xyLen a d + xyLen b c < xyLen a c + xyLen b d := by
  have hp := E97BlockB.diagonal_parameters_in_unit_interval
    a b c d habc habd hbcd hacd
  change 0 < diagT a b c d / diagDelta a b c d ∧
    diagT a b c d / diagDelta a b c d < 1 ∧
    0 < diagS a b c d / diagDelta a b c d ∧
    diagS a b c d / diagDelta a b c d < 1 at hp
  rcases hp with ⟨ht,ht1,hs,hs1⟩
  let t : ℝ := diagT a b c d / diagDelta a b c d
  let s : ℝ := diagS a b c d / diagDelta a b c d
  let x : XY := onChord a c t
  have hdelta : 0 < diagDelta a b c d := by
    have h := E97BlockB.diagonal_delta_minus_t a b c d
    have heq := E97BlockB.diagonal_t_is_orientation a b c d
    rw [heq] at h
    linarith
  have hx : x = onChord b d s := two_diagonals_meet a b c d hdelta
  have hac : xyLen a x + xyLen x c = xyLen a c :=
    xyLen_onChord_add a c t (le_of_lt ht) (le_of_lt ht1)
  have hbd : xyLen b x + xyLen x d = xyLen b d := by
    rw [hx]
    exact xyLen_onChord_add b d s (le_of_lt hs) (le_of_lt hs1)
  have hab_or : orient a x b ≠ 0 := by
    have heq : orient a x b = -(t * orient a b c) := by
      dsimp [x, onChord, orient]
      ring
    rw [heq]
    have hm := mul_pos ht habc
    linarith
  have hcd_or : orient c x d ≠ 0 := by
    have heq : orient c x d = -((1-t) * orient a c d) := by
      dsimp [x, onChord, orient]
      ring
    rw [heq]
    have hm := mul_pos (sub_pos.mpr ht1) hacd
    linarith
  have hbc_or : orient b x c ≠ 0 := by
    have heq : orient b x c = -(s * orient b c d) := by
      rw [hx]
      dsimp [onChord, orient]
      ring
    rw [heq]
    have hm := mul_pos hs hbcd
    linarith
  have hda_or : orient d x a ≠ 0 := by
    have heq : orient d x a = -((1-s) * orient a b d) := by
      rw [hx]
      dsimp [onChord, orient]
      ring
    rw [heq]
    have hm := mul_pos (sub_pos.mpr hs1) habd
    linarith
  have hab : xyLen a b < xyLen a x + xyLen x b :=
    strict_triangle_of_nonnezero_orient a x b hab_or
  have hcd : xyLen c d < xyLen c x + xyLen x d :=
    strict_triangle_of_nonnezero_orient c x d hcd_or
  have hbc : xyLen b c < xyLen b x + xyLen x c :=
    strict_triangle_of_nonnezero_orient b x c hbc_or
  have hda : xyLen d a < xyLen d x + xyLen x a :=
    strict_triangle_of_nonnezero_orient d x a hda_or
  have hba : xyLen x b = xyLen b x := xyLen_symm x b
  have hca : xyLen c x = xyLen x c := xyLen_symm c x
  have hdx : xyLen d x = xyLen x d := xyLen_symm d x
  have hxa : xyLen x a = xyLen a x := xyLen_symm x a
  have had : xyLen d a = xyLen a d := xyLen_symm d a
  constructor <;> linarith

#print axioms E97ConvexQuad12.sqDist_onChord_left
#print axioms E97ConvexQuad12.sqDist_onChord_right
#print axioms E97ConvexQuad12.xyLen_onChord_left
#print axioms E97ConvexQuad12.xyLen_onChord_right
#print axioms E97ConvexQuad12.xyLen_onChord_add
#print axioms E97ConvexQuad12.two_diagonals_meet
#print axioms E97ConvexQuad12.convex_quad_strict
end E97ConvexQuad12
