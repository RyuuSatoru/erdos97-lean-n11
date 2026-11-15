import Mathlib

/-!
Erdos97 / Block B: coordinate geometry, independent of certificate tables.
No `sorry` or additional axioms. CANDIDATE: this file has NOT been compiled
with Lean in the assistant's environment; use the supplied Modal notebook.
The strict convexity hypothesis for these coordinates must be supplied by
orientations of all cyclically ordered triples, not just successive triples.
-/
set_option autoImplicit false
namespace E97BlockB

abbrev XY := ℝ × ℝ

def orient (a b c : XY) : ℝ :=
  (b.1-a.1)*(c.2-a.2) - (b.2-a.2)*(c.1-a.1)

def sqDist (a b : XY) : ℝ :=
  (a.1-b.1)^2+(a.2-b.2)^2

/-- Elementary squared-distance identity for a perpendicular bisector. -/
theorem perpendicular_bisector_identity (a b x : XY) :
    sqDist x a - sqDist x b =
    2*((x.1-(a.1+b.1)/2)*(b.1-a.1) +
       (x.2-(a.2+b.2)/2)*(b.2-a.2)) := by
  dsimp [sqDist]
  ring

/-- Determinant of the diagonal directions. -/
def diagDelta (a b c d : XY) : ℝ :=
  (c.1-a.1)*(d.2-b.2)-(c.2-a.2)*(d.1-b.1)
def diagT (a b _c d : XY) : ℝ :=
  (b.1-a.1)*(d.2-b.2)-(b.2-a.2)*(d.1-b.1)
def diagS (a b c _d : XY) : ℝ :=
  (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1)

/-- Diagonal intersection numerator identity, x-coordinate. -/
theorem diagonal_cross_x (a b c d : XY) :
    diagT a b c d * (c.1-a.1) - diagS a b c d*(d.1-b.1) =
      diagDelta a b c d*(b.1-a.1) := by
  dsimp [diagT, diagS, diagDelta]
  ring

/-- Diagonal intersection numerator identity, y-coordinate. -/
theorem diagonal_cross_y (a b c d : XY) :
    diagT a b c d * (c.2-a.2) - diagS a b c d*(d.2-b.2) =
      diagDelta a b c d*(b.2-a.2) := by
  dsimp [diagT, diagS, diagDelta]
  ring

/-- Orientation facts convert directly to numerator inequalities. -/
theorem diagonal_delta_minus_t (a b c d : XY) :
    diagDelta a b c d - diagT a b c d = orient b c d := by
  dsimp [diagDelta, diagT, orient]
  ring

theorem diagonal_delta_minus_s (a b c d : XY) :
    diagDelta a b c d - diagS a b c d = orient a c d := by
  dsimp [diagDelta, diagS, orient]
  ring

theorem diagonal_t_is_orientation (a b c d : XY) :
    diagT a b c d = orient a b d := by
  dsimp [diagT, orient]
  ring

theorem diagonal_s_is_orientation (a b c d : XY) :
    diagS a b c d = orient a b c := by
  rfl

/-- The intersection parameters both lie strictly in (0,1).
This is the nontrivial intersection-existence step needed before A4. -/
theorem diagonal_parameters_in_unit_interval (a b c d : XY)
  (h₁ : 0 < orient a b c) (h₂ : 0 < orient a b d)
  (h₃ : 0 < orient b c d) (h₄ : 0 < orient a c d) :
  let t := diagT a b c d
  let s := diagS a b c d
  let Δ := diagDelta a b c d
  0 < t/Δ ∧ t/Δ < 1 ∧ 0 < s/Δ ∧ s/Δ < 1 := by
  dsimp
  have ht : 0 < diagT a b c d := by
    rw [diagonal_t_is_orientation]
    exact h₂
  have hs : 0 < diagS a b c d := by
    rw [diagonal_s_is_orientation]
    exact h₁
  have hdt : 0 < diagDelta a b c d - diagT a b c d := by
    rw [diagonal_delta_minus_t]
    exact h₃
  have hds : 0 < diagDelta a b c d - diagS a b c d := by
    rw [diagonal_delta_minus_s]
    exact h₄
  have hΔ : 0 < diagDelta a b c d := by linarith
  constructor
  · exact div_pos ht hΔ
  constructor
  · apply (div_lt_iff₀ hΔ).2
    linarith
  constructor
  · exact div_pos hs hΔ
  · apply (div_lt_iff₀ hΔ).2
    linarith

/-- This theorem is the final *metric* argument behind A4: strict
triangle inequalities at the actual crossing point imply both A4 forms. -/
theorem quadrilateral_from_diagonal_triangles
  (AC BD AB BC CD DA AX BX CX DX : ℝ)
  (hAC : AC = AX+CX) (hBD : BD=BX+DX)
  (hAB : AB < AX+BX) (hBC : BC < BX+CX)
  (hCD : CD < CX+DX) (hDA : DA < DX+AX) :
  AB+CD < AC+BD ∧ DA+BC < AC+BD := by
  constructor <;> linarith

#print axioms E97BlockB.diagonal_parameters_in_unit_interval
#print axioms E97BlockB.quadrilateral_from_diagonal_triangles
end E97BlockB
