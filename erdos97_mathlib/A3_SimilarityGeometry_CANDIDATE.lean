import BlockB_EuclideanGeometry_CANDIDATE
import A3_GeneralAlgebra_CANDIDATE

/-!
A3 geometric bridge for ANY planar points P,A,B,C,Q, not only
pre-normalized coordinates. The map z |-> (dot(B-A,z-A), det(B-A,z-A))
is a polynomial rotation-plus-scaling that maps A to 0 and B to
(d,0), d = squared Euclidean length |B-A|^2 > 0.
It preserves all orientation signs and squared-distance comparisons.
CANDIDATE: not yet Lean kernel checked.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97A3
open E97BlockB

def rotatedScaled (a b z : XY) : XY :=
  ((b.1-a.1)*(z.1-a.1)+(b.2-a.2)*(z.2-a.2),
   (b.1-a.1)*(z.2-a.2)-(b.2-a.2)*(z.1-a.1))

theorem rotatedScaled_anchor_a (a b : XY) :
    rotatedScaled a b a = (0,0) := by
  apply Prod.ext <;> dsimp [rotatedScaled] <;> ring

theorem rotatedScaled_anchor_b (a b : XY) :
    rotatedScaled a b b = (sqDist a b,0) := by
  apply Prod.ext
  · dsimp [rotatedScaled, sqDist]
    ring
  · dsimp [rotatedScaled]
    ring

theorem rotatedScaled_sqDist (a b z w : XY) :
    sqDist (rotatedScaled a b z) (rotatedScaled a b w) =
      sqDist a b * sqDist z w := by
  dsimp [rotatedScaled, sqDist]
  ring

theorem rotatedScaled_orient (a b z w k : XY) :
    orient (rotatedScaled a b z) (rotatedScaled a b w)
      (rotatedScaled a b k) = sqDist a b * orient z w k := by
  dsimp [rotatedScaled, sqDist, orient]
  ring

theorem sqDist_pos_of_ne (a b : XY) (hne : a ≠ b) :
    0 < sqDist a b := by
  by_contra hnot
  have hle : sqDist a b ≤ 0 := le_of_not_gt hnot
  have hs : (a.1-b.1)^2 + (a.2-b.2)^2 ≤ 0 := by
    simpa only [sqDist] using hle
  have hx : a.1=b.1 := by
    nlinarith [sq_nonneg (a.1-b.1), sq_nonneg (a.2-b.2)]
  have hy : a.2=b.2 := by
    nlinarith [sq_nonneg (a.1-b.1), sq_nonneg (a.2-b.2)]
  exact hne (Prod.ext hx hy)

private theorem positive_factor_right (d x : ℝ)
    (hd : 0 < d) (hdx : 0 < d*x) : 0 < x := by
  by_contra hnot
  have hle : x ≤ 0 := le_of_not_gt hnot
  have hprod : d*x ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hd) hle
  linarith

/-- A3 for arbitrary real Euclidean coordinates and the six necessary
CCW orientation conditions of cyclic order P,A,B,C,Q.
Equality of SQUARED distances is equivalent to ordinary distance equality.
CA ≤ CB is likewise encoded by the squared-distance inequality. -/
theorem five_point_euclidean_impossible
    (p a b c q : XY)
    (hPAB : 0 < orient p a b)
    (hABC : 0 < orient a b c)
    (hABQ : 0 < orient a b q)
    (hPAQ : 0 < orient p a q)
    (hACQ : 0 < orient a c q)
    (hBCQ : 0 < orient b c q)
    (hBP : sqDist b p = sqDist b a)
    (hCQ : sqDist c q = sqDist c a)
    (hCAleCB : sqDist c a ≤ sqDist c b) : False := by
  have habne : a ≠ b := by
    intro hab
    rw [hab] at hPAB
    have hzero : orient p b b = 0 := by
      dsimp [orient]
      ring
    linarith
  let D : ℝ := sqDist a b
  let PP : XY := rotatedScaled a b p
  let CC : XY := rotatedScaled a b c
  let QQ : XY := rotatedScaled a b q
  have hD : 0 < D := sqDist_pos_of_ne a b habne
  have hPP : 0 < orient PP (0,0) (D,0) := by
    have hh : 0 < orient (rotatedScaled a b p)
        (rotatedScaled a b a) (rotatedScaled a b b) := by
      rw [rotatedScaled_orient]
      exact mul_pos hD hPAB
    simpa only [rotatedScaled_anchor_a, rotatedScaled_anchor_b] using hh
  have hCC : 0 < orient (0,0) (D,0) CC := by
    have hh : 0 < orient (rotatedScaled a b a)
        (rotatedScaled a b b) (rotatedScaled a b c) := by
      rw [rotatedScaled_orient]
      exact mul_pos hD hABC
    simpa only [rotatedScaled_anchor_a, rotatedScaled_anchor_b] using hh
  have hQQ : 0 < orient (0,0) (D,0) QQ := by
    have hh : 0 < orient (rotatedScaled a b a)
        (rotatedScaled a b b) (rotatedScaled a b q) := by
      rw [rotatedScaled_orient]
      exact mul_pos hD hABQ
    simpa only [rotatedScaled_anchor_a, rotatedScaled_anchor_b] using hh
  have hPAQ' : 0 < orient PP (0,0) QQ := by
    have hh : 0 < orient (rotatedScaled a b p)
        (rotatedScaled a b a) (rotatedScaled a b q) := by
      rw [rotatedScaled_orient]
      exact mul_pos hD hPAQ
    simpa only [rotatedScaled_anchor_a] using hh
  have hACQ' : 0 < orient (0,0) CC QQ := by
    have hh : 0 < orient (rotatedScaled a b a)
        (rotatedScaled a b c) (rotatedScaled a b q) := by
      rw [rotatedScaled_orient]
      exact mul_pos hD hACQ
    simpa only [rotatedScaled_anchor_a] using hh
  have hBCQ' : 0 < orient (D,0) CC QQ := by
    have hh : 0 < orient (rotatedScaled a b b)
        (rotatedScaled a b c) (rotatedScaled a b q) := by
      rw [rotatedScaled_orient]
      exact mul_pos hD hBCQ
    simpa only [rotatedScaled_anchor_b] using hh
  have hyProd : 0 < D*PP.2 := by
    have hf : orient PP (0,0) (D,0) = D*PP.2 := by
      dsimp [orient]
      ring
    rw [hf] at hPP
    exact hPP
  have hhProd : 0 < D*CC.2 := by
    have hf : orient (0,0) (D,0) CC = D*CC.2 := by
      dsimp [orient]
      ring
    rw [hf] at hCC
    exact hCC
  have hvProd : 0 < D*QQ.2 := by
    have hf : orient (0,0) (D,0) QQ = D*QQ.2 := by
      dsimp [orient]
      ring
    rw [hf] at hQQ
    exact hQQ
  have hy : 0 < PP.2 := positive_factor_right D PP.2 hD hyProd
  have hh : 0 < CC.2 := positive_factor_right D CC.2 hD hhProd
  have hv : 0 < QQ.2 := positive_factor_right D QQ.2 hD hvProd
  have hs : 0 < QQ.1*PP.2-QQ.2*PP.1 := by
    have hf : orient PP (0,0) QQ = QQ.1*PP.2-QQ.2*PP.1 := by
      dsimp [orient]
      ring
    rw [hf] at hPAQ'
    exact hPAQ'
  have hw : 0 < CC.1*QQ.2-CC.2*QQ.1 := by
    have hf : orient (0,0) CC QQ = CC.1*QQ.2-CC.2*QQ.1 := by
      dsimp [orient]
      ring
    rw [hf] at hACQ'
    exact hACQ'
  have hz : 0 < CC.2*(D-QQ.1)-(D-CC.1)*QQ.2 := by
    have hf : orient (D,0) CC QQ =
        CC.2*(D-QQ.1)-(D-CC.1)*QQ.2 := by
      dsimp [orient]
      ring
    rw [hf] at hBCQ'
    exact hBCQ'
  have hBP' : sqDist (D,0) PP = sqDist (D,0) (0,0) := by
    have heq : sqDist (rotatedScaled a b b) (rotatedScaled a b p) =
        sqDist (rotatedScaled a b b) (rotatedScaled a b a) := by
      rw [rotatedScaled_sqDist, rotatedScaled_sqDist, hBP]
    simpa only [rotatedScaled_anchor_a, rotatedScaled_anchor_b] using heq
  have hCQ' : sqDist CC QQ = sqDist CC (0,0) := by
    have heq : sqDist (rotatedScaled a b c) (rotatedScaled a b q) =
        sqDist (rotatedScaled a b c) (rotatedScaled a b a) := by
      rw [rotatedScaled_sqDist, rotatedScaled_sqDist, hCQ]
    simpa only [rotatedScaled_anchor_a] using heq
  have hCA' : sqDist CC (0,0) ≤ sqDist CC (D,0) := by
    calc
      sqDist CC (0,0) = D*sqDist c a := by
        simpa only [rotatedScaled_anchor_a] using
          (rotatedScaled_sqDist a b c a)
      _ ≤ D*sqDist c b := mul_le_mul_of_nonneg_left hCAleCB (le_of_lt hD)
      _ = sqDist CC (D,0) := by
        simpa only [rotatedScaled_anchor_b] using
          (rotatedScaled_sqDist a b c b).symm
  have he1 : 2*D*PP.1-PP.1^2-PP.2^2 = 0 := by
    dsimp [sqDist] at hBP'
    nlinarith [hBP']
  have he2 : QQ.1^2+QQ.2^2-2*CC.1*QQ.1-2*CC.2*QQ.2 = 0 := by
    dsimp [sqDist] at hCQ'
    nlinarith [hCQ']
  have hrD : 0 ≤ D*(D-2*CC.1) := by
    dsimp [sqDist] at hCA'
    nlinarith [hCA']
  have hr : 0 ≤ D-2*CC.1 := by
    by_contra hnot
    have hneg : D-2*CC.1 < 0 := lt_of_not_ge hnot
    have hprod : D*(D-2*CC.1) < 0 := mul_neg_of_pos_of_neg hD hneg
    linarith
  exact five_point_scaled_algebra D PP.1 PP.2 CC.1 CC.2 QQ.1 QQ.2
    hD hy hh hv hs hw hz hr he1 he2

#print axioms E97A3.rotatedScaled_sqDist
#print axioms E97A3.rotatedScaled_orient
#print axioms E97A3.five_point_euclidean_impossible
end E97A3
