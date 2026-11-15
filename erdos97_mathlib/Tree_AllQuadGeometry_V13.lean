import Tree_FirstF_StrictCCW_V12_CANDIDATE

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace E97AllQuad13
open E97BlockB E97Geo12 E97FirstFGeometry10 E97TreeMetricV8

def endpoints (e : Nat) : Nat × Nat :=
  (E97A2Rows.edgeEndpoints[e]?).getD (0,0)

/-- The actual table entry must be one of the two strict convex quad shapes. -/
def QuadShape (q : Nat) : Prop :=
  let (a,b,c,d) := E97Flow.getQuad q
  let (i,k) := endpoints a
  let (j,l) := endpoints b
  i < j ∧ j < k ∧ k < l ∧ l < 11 ∧
    ((endpoints c = (i,j) ∧ endpoints d = (k,l)) ∨
     (endpoints c = (i,l) ∧ endpoints d = (j,k)))

instance (q : Nat) : Decidable (QuadShape q) := by
  unfold QuadShape
  infer_instance

theorem all_quad_shapes :
    (List.range 660).all (fun q => decide (QuadShape q)) = true := by
  decide +kernel

theorem quad_shape (q : Nat) (hq : q < 660) : QuadShape q := by
  exact decide_eq_true_eq.mp
    ((List.all_eq_true.mp all_quad_shapes) q (List.mem_range.mpr hq))

/-- Strict positivity for every actual A4 entry, from strict CCW alone. -/
theorem all_actual_quad_gaps_positive (P : Fin 11 → XY)
    (hccw : E97A1Index.StrictCCW11 P) (q : Nat) (hq : q < 660) :
    0 < actualQuadGap (edgeLength P) q := by
  have hs := quad_shape q hq
  rcases hquad : E97Flow.getQuad q with ⟨a,b,c,d⟩
  rcases ha : endpoints a with ⟨i,k⟩
  rcases hb : endpoints b with ⟨j,l⟩
  simp only [QuadShape, hquad, ha, hb] at hs
  obtain ⟨hij,hjk,hkl,hl,hsides⟩ := hs
  have hstrict := E97ActualFirstF12.ccw11_quad_strict P hccw i j k l hij hjk hkl hl
  change (E97A2Rows.edgeEndpoints[a]?).getD (0,0) = (i,k) at ha
  change (E97A2Rows.edgeEndpoints[b]?).getD (0,0) = (j,l) at hb
  rcases hsides with ⟨hc,hd⟩ | ⟨hc,hd⟩
  · change (E97A2Rows.edgeEndpoints[c]?).getD (0,0) = (i,j) at hc
    change (E97A2Rows.edgeEndpoints[d]?).getD (0,0) = (k,l) at hd
    simp only [actualQuadGap, hquad, edgeLength, edgeSquare, ha, hb, hc, hd]
    change 0 < xyLen (P (Fin.ofNat 11 i)) (P (Fin.ofNat 11 k)) +
      xyLen (P (Fin.ofNat 11 j)) (P (Fin.ofNat 11 l)) -
      xyLen (P (Fin.ofNat 11 i)) (P (Fin.ofNat 11 j)) -
      xyLen (P (Fin.ofNat 11 k)) (P (Fin.ofNat 11 l))
    linarith [hstrict.1]
  · change (E97A2Rows.edgeEndpoints[c]?).getD (0,0) = (i,l) at hc
    change (E97A2Rows.edgeEndpoints[d]?).getD (0,0) = (j,k) at hd
    simp only [actualQuadGap, hquad, edgeLength, edgeSquare, ha, hb, hc, hd]
    change 0 < xyLen (P (Fin.ofNat 11 i)) (P (Fin.ofNat 11 k)) +
      xyLen (P (Fin.ofNat 11 j)) (P (Fin.ofNat 11 l)) -
      xyLen (P (Fin.ofNat 11 i)) (P (Fin.ofNat 11 l)) -
      xyLen (P (Fin.ofNat 11 j)) (P (Fin.ofNat 11 k))
    linarith [hstrict.2]

#print axioms E97AllQuad13.all_quad_shapes
#print axioms E97AllQuad13.quad_shape
#print axioms E97AllQuad13.all_actual_quad_gaps_positive
end E97AllQuad13
