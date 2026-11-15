import BlockB_EuclideanGeometry_CANDIDATE

/-!
Erdos #97: geometric A1 kernel candidate.

If two distinct points U and V have the same distances from two centers A
and B, then the orientation of U about the directed line AB is the negative
of the orientation of V.  Thus, if the line AB is nondegenerate and neither
witness is collinear with it, the witnesses are on opposite sides.

This is the geometric component of the two-center crossing filter A1.
The separate finite index lemma translating opposite sides to cyclic
alternation of vertex labels is NOT proved here.

Candidate until compiled in Lean/Mathlib. No `sorry`, no additional axioms.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace E97A1
open E97BlockB

/-- In R^2, two vectors orthogonal to the same nonzero vector are parallel. -/
theorem planar_orthogonal_parallel
    (tx ty sx sy dx dy : ℝ)
    (hT : tx*dx + ty*dy = 0)
    (hS : sx*dx + sy*dy = 0)
    (hD : dx*dx + dy*dy ≠ 0) :
    tx*sy - ty*sx = 0 := by
  have hident :
      (tx*sy - ty*sx)*(dx*dx + dy*dy) =
        (tx*dx + ty*dy)*(dx*sy - dy*sx) -
        (sx*dx + sy*dy)*(dx*ty - dy*tx) := by
    ring
  rw [hT, hS] at hident
  have hzero : (tx*sy - ty*sx)*(dx*dx + dy*dy) = 0 := by
    simpa only [zero_mul, sub_self] using hident
  rcases mul_eq_zero.mp hzero with h | h
  · exact h
  · exact False.elim (hD h)

/-- The difference vector U-V has nonzero squared norm if U!=V. -/
theorem squared_displacement_ne_zero (u v : XY) (hneq : u ≠ v) :
    (u.1-v.1)^2 + (u.2-v.2)^2 ≠ 0 := by
  intro hsum
  have hx : u.1-v.1 = 0 := by
    nlinarith [sq_nonneg (u.1-v.1), sq_nonneg (u.2-v.2)]
  have hy : u.2-v.2 = 0 := by
    nlinarith [sq_nonneg (u.1-v.1), sq_nonneg (u.2-v.2)]
  have huv : u = v := Prod.ext (by linarith) (by linarith)
  exact hneq huv

/-- A1 perpendicular-bisector fact with the actual Euclidean squared
    distance and signed orientation, with no genericity assumption on A,B. -/
theorem shared_witnesses_orientation_opposite
    (a b u v : XY) (huv : u ≠ v)
    (ha : sqDist a u = sqDist a v)
    (hb : sqDist b u = sqDist b v) :
    orient a b u = -orient a b v := by
  have hAu :
      (u.1-v.1)*(u.1+v.1-2*a.1) +
      (u.2-v.2)*(u.2+v.2-2*a.2) = 0 := by
    dsimp [sqDist] at ha
    nlinarith [ha]
  have hBu :
      (u.1-v.1)*(u.1+v.1-2*b.1) +
      (u.2-v.2)*(u.2+v.2-2*b.2) = 0 := by
    dsimp [sqDist] at hb
    nlinarith [hb]
  have hTU :
      (b.1-a.1)*(u.1-v.1) + (b.2-a.2)*(u.2-v.2) = 0 := by
    nlinarith [hAu,hBu]
  have hD : (u.1-v.1)*(u.1-v.1) +
      (u.2-v.2)*(u.2-v.2) ≠ 0 := by
    simpa only [pow_two] using squared_displacement_ne_zero u v huv
  have hAu_comm :
      (u.1+v.1-2*a.1)*(u.1-v.1) +
      (u.2+v.2-2*a.2)*(u.2-v.2) = 0 := by
    calc
      (u.1+v.1-2*a.1)*(u.1-v.1) +
          (u.2+v.2-2*a.2)*(u.2-v.2) =
        (u.1-v.1)*(u.1+v.1-2*a.1) +
          (u.2-v.2)*(u.2+v.2-2*a.2) := by ring
      _ = 0 := hAu
  have hCross := planar_orthogonal_parallel
    (b.1-a.1) (b.2-a.2)
    (u.1+v.1-2*a.1) (u.2+v.2-2*a.2)
    (u.1-v.1) (u.2-v.2) hTU hAu_comm hD
  have hsum : orient a b u + orient a b v = 0 := by
    dsimp [orient]
    nlinarith [hCross]
  linarith

/-- A1: when one shared witness lies strictly to the left of AB,
    the other lies strictly to the right. -/
theorem shared_witnesses_opposite_sides
    (a b u v : XY) (huv : u ≠ v)
    (ha : sqDist a u = sqDist a v)
    (hb : sqDist b u = sqDist b v)
    (hu : 0 < orient a b u) : orient a b v < 0 := by
  have h := shared_witnesses_orientation_opposite a b u v huv ha hb
  linarith

#print axioms E97A1.planar_orthogonal_parallel
#print axioms E97A1.squared_displacement_ne_zero
#print axioms E97A1.shared_witnesses_orientation_opposite
#print axioms E97A1.shared_witnesses_opposite_sides
end E97A1
