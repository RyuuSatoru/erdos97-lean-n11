import AllowFiniteReasonCore_CANDIDATE
/-!
Decode the *specific* A1 and A3 branches of the finite checker.
These are transport lemmas, not full table coverage.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace E97ReasonPayload
open E97AllowFinite
/-- If checkReason accepts a nonzero A1 code, the precise three tests are true. -/
theorem a1_payload (slot code : Nat)
  (hs : slot < 2425500) (hc0 : 0 < code) (hc1 : code ≤ 55)
  (h : checkReason slot code = true) :
  (let (a,b,_x,_y,ma,mb) := cellData slot
   let (u,v) := pairAt (code - 1)
   containsBits ma ((2 ^ u) ||| (2 ^ v)) &&
   containsBits mb ((2 ^ u) ||| (2 ^ v)) &&
   (alternate a b u v == false)) = true := by
  have hn : code ≠ 0 := Nat.ne_of_gt hc0
  unfold checkReason at h
  simp only [ite_eq_left hs, ite_eq_right hn, ite_eq_left hc1] at h
  exact h

/-- A3 branch of finite checker, including its center-order flip. -/
theorem a3_payload (slot code : Nat)
  (hs : slot < 2425500) (hc0 : 55 < code) (hc1 : code ≤ 4675)
  (h : checkReason slot code = true) :
  (let (a,b,_x,_y,ma,mb) := cellData slot
   let pat := patternAt (code - 56)
   if pat.c = a ∧ pat.d = b then
     containsBits ma pat.mc && containsBits mb pat.md
   else if pat.c = b ∧ pat.d = a then
     containsBits mb pat.mc && containsBits ma pat.md
   else false) = true := by
  have hcpos : 0 < code := lt_trans (by decide : 0 < 55) hc0
  have hn : code ≠ 0 := Nat.ne_of_gt hcpos
  have hn55 : ¬ code ≤ 55 := Nat.not_le.mpr hc0
  unfold checkReason at h
  simp only [ite_eq_left hs, ite_eq_right hn, ite_eq_right hn55, ite_eq_left hc1] at h
  exact h
#print axioms E97ReasonPayload.a1_payload
#print axioms E97ReasonPayload.a3_payload
end E97ReasonPayload
