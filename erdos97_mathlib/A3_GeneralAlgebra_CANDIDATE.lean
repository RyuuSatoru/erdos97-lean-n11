import Mathlib

/-!
Erdos #97 A3: the five-point contradiction in rotated-scaled coordinates.
Unlike the earlier normalized A=(0,0), B=(1,0) proof, B=(d,0)
for arbitrary d>0; this permits a POLYNOMIAL similarity, with no division,
square roots, or an assumption that the original A,B are axis aligned.
This file is a CANDIDATE until compiled by Lean on Modal.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97A3

/-- A3 algebra, for P=(x,y), A=(0,0), B=(d,0), C=(t,h), Q=(u,v).
The orientation signs are exactly those of cyclic order P,A,B,C,Q. -/
theorem five_point_scaled_algebra
    (d x y t h u v : ℝ)
    (hd : 0 < d)
    (hy : 0 < y) (hh : 0 < h) (hv : 0 < v)
    (hs : 0 < u*y-v*x)
    (hw : 0 < t*v-h*u)
    (hz : 0 < h*(d-u)-(d-t)*v)
    (hr : 0 ≤ d-2*t)
    (he1 : 2*d*x-x^2-y^2 = 0)
    (he2 : u^2+v^2-2*t*u-2*h*v = 0) : False := by
  have hx : 0 < x := by
    by_contra hnot
    have hx0 : x ≤ 0 := le_of_not_gt hnot
    have hdx : d*x ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hd) hx0
    have hy2 : 0 < y*y := mul_pos hy hy
    nlinarith [sq_nonneg x]
  have hu : 0 < u := by
    by_contra hnot
    have hu0 : u ≤ 0 := le_of_not_gt hnot
    have hUY : u*y ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hu0 (le_of_lt hy)
    have hVX : 0 < v*x := mul_pos hv hx
    linarith
  have ht : 0 < t := by
    by_contra hnot
    have ht0 : t ≤ 0 := le_of_not_gt hnot
    have hTV : t*v ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg ht0 (le_of_lt hv)
    have hHU : 0 < h*u := mul_pos hh hu
    linarith
  have hRV : 0 ≤ (d-2*t)*v := mul_nonneg hr (le_of_lt hv)
  have hHU : 0 < h*u := mul_pos hh hu
  have hZ2 : 0 < 2*(h*(d-u)-(d-t)*v) := by linarith
  have hHidentity :
      d*(2*h-v) = 2*(h*(d-u)-(d-t)*v) + 2*h*u + (d-2*t)*v := by
    ring
  have hdH : 0 < d*(2*h-v) := by
    rw [hHidentity]
    linarith
  have hH : 0 < 2*h-v := by
    by_contra hnot
    have hle : 2*h-v ≤ 0 := le_of_not_gt hnot
    have hprod : d*(2*h-v) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hd) hle
    linarith
  have hM : 0 < u*t+h*v :=
    add_pos (mul_pos hu ht) (mul_pos hh hv)
  have hp1 : 0 < (u*t+h*v)*(2*h-v) := mul_pos hM hH
  have hp2 : 0 < u*(t*v-h*u) := mul_pos hu hw
  have hidentity :
      h*(u^2+v^2-2*t*u-2*h*v) +
        u*(t*v-h*u) + (u*t+h*v)*(2*h-v) = 0 := by ring
  rw [he2] at hidentity
  simp only [mul_zero, zero_add] at hidentity
  linarith

#print axioms E97A3.five_point_scaled_algebra
end E97A3
