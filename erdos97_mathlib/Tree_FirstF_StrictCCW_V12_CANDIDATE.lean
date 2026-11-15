import Tree_ConvexQuad_V12_CANDIDATE
import Tree_FirstF_RowGeometry_V10_CANDIDATE

/-!
E97 V12 stage 3: exact index-level bridge. q=14,288,655 are three
quadTable entries in the first REAL F leaf of the canonical tree. All three
are positive from StrictCCW11, WITHOUT assuming `actualQuadGap > 0`.
If this module passes, the first F leaf is geometrically closed in Lean
under only strict convexity and four actual selected-row realizations.
No statement about all K/F leaves or full-tree parsing/completeness.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97ActualFirstF12
open E97BlockB E97Geo12 E97ConvexQuad12 E97FirstFGeometry10 E97TreeMetricV8

/-- Pin the three F quad indices directly to the canonical Lean table. -/
theorem firstF_quad_indices_exact :
    E97Flow.getQuad 14 = (1,18,0,26) ∧
    E97Flow.getQuad 288 = (15,26,10,51) ∧
    E97Flow.getQuad 655 = (47,51,48,50) := by
  decide +kernel

/-- Pin all twelve actual source edge endpoints: these are not user-given
arithmetic assumptions but kernel-reduced facts about the 55-edge table. -/
theorem firstF_quad_endpoints_exact :
    (E97A2Rows.edgeEndpoints[1]?).getD (0,0) = (0,2) ∧
    (E97A2Rows.edgeEndpoints[18]?).getD (0,0) = (1,10) ∧
    (E97A2Rows.edgeEndpoints[0]?).getD (0,0) = (0,1) ∧
    (E97A2Rows.edgeEndpoints[26]?).getD (0,0) = (2,10) ∧
    (E97A2Rows.edgeEndpoints[15]?).getD (0,0) = (1,7) ∧
    (E97A2Rows.edgeEndpoints[10]?).getD (0,0) = (1,2) ∧
    (E97A2Rows.edgeEndpoints[51]?).getD (0,0) = (7,10) ∧
    (E97A2Rows.edgeEndpoints[47]?).getD (0,0) = (6,9) ∧
    (E97A2Rows.edgeEndpoints[48]?).getD (0,0) = (6,10) ∧
    (E97A2Rows.edgeEndpoints[50]?).getD (0,0) = (7,9) := by
  decide +kernel

/-- Four ordered distinct vertices of StrictCCW11 form a strict
Euclidean quadrilateral with diagonals longer in total than either
opposite pair of sides. -/
theorem ccw11_quad_strict (P : Fin 11 → XY)
    (hccw : E97A1Index.StrictCCW11 P)
    (i j k l : Nat) (hij : i < j) (hjk : j < k)
    (hkl : k < l) (hl : l < 11) :
    xyLen (P (Fin.ofNat 11 i)) (P (Fin.ofNat 11 j)) +
      xyLen (P (Fin.ofNat 11 k)) (P (Fin.ofNat 11 l)) <
      xyLen (P (Fin.ofNat 11 i)) (P (Fin.ofNat 11 k)) +
      xyLen (P (Fin.ofNat 11 j)) (P (Fin.ofNat 11 l)) ∧
    xyLen (P (Fin.ofNat 11 i)) (P (Fin.ofNat 11 l)) +
      xyLen (P (Fin.ofNat 11 j)) (P (Fin.ofNat 11 k)) <
      xyLen (P (Fin.ofNat 11 i)) (P (Fin.ofNat 11 k)) +
      xyLen (P (Fin.ofNat 11 j)) (P (Fin.ofNat 11 l)) := by
  exact convex_quad_strict _ _ _ _
    (hccw i j k hij hjk (by omega))
    (hccw i j l hij (by omega) hl)
    (hccw j k l hjk hkl hl)
    (hccw i k l (by omega) hkl hl)

/-- getQuad 14 = (1,18,0,26): the two diagonals (0,2), (1,10)
minus the opposite sides (0,1), (2,10). -/
theorem actual_gap_14_positive (P : Fin 11 → XY)
    (hccw : E97A1Index.StrictCCW11 P) :
    0 < actualQuadGap (edgeLength P) 14 := by
  have h := (ccw11_quad_strict P hccw 0 1 2 10
    (by omega) (by omega) (by omega) (by omega)).1
  change 0 <
    xyLen (P (Fin.ofNat 11 0)) (P (Fin.ofNat 11 2)) +
    xyLen (P (Fin.ofNat 11 1)) (P (Fin.ofNat 11 10)) -
    xyLen (P (Fin.ofNat 11 0)) (P (Fin.ofNat 11 1)) -
    xyLen (P (Fin.ofNat 11 2)) (P (Fin.ofNat 11 10))
  linarith

/-- getQuad 288 = (15,26,10,51): diagonals (1,7), (2,10)
minus opposite sides (1,2), (7,10). -/
theorem actual_gap_288_positive (P : Fin 11 → XY)
    (hccw : E97A1Index.StrictCCW11 P) :
    0 < actualQuadGap (edgeLength P) 288 := by
  have h := (ccw11_quad_strict P hccw 1 2 7 10
    (by omega) (by omega) (by omega) (by omega)).1
  change 0 <
    xyLen (P (Fin.ofNat 11 1)) (P (Fin.ofNat 11 7)) +
    xyLen (P (Fin.ofNat 11 2)) (P (Fin.ofNat 11 10)) -
    xyLen (P (Fin.ofNat 11 1)) (P (Fin.ofNat 11 2)) -
    xyLen (P (Fin.ofNat 11 7)) (P (Fin.ofNat 11 10))
  linarith

/-- getQuad 655 = (47,51,48,50): diagonals (6,9), (7,10)
minus the OTHER opposite side pair (6,10), (7,9). -/
theorem actual_gap_655_positive (P : Fin 11 → XY)
    (hccw : E97A1Index.StrictCCW11 P) :
    0 < actualQuadGap (edgeLength P) 655 := by
  have h := (ccw11_quad_strict P hccw 6 7 9 10
    (by omega) (by omega) (by omega) (by omega)).2
  change 0 <
    xyLen (P (Fin.ofNat 11 6)) (P (Fin.ofNat 11 9)) +
    xyLen (P (Fin.ofNat 11 7)) (P (Fin.ofNat 11 10)) -
    xyLen (P (Fin.ofNat 11 6)) (P (Fin.ofNat 11 10)) -
    xyLen (P (Fin.ofNat 11 7)) (P (Fin.ofNat 11 9))
  linarith

/-- First true F record q={14,288,655}: all three geometric
positivity assumptions of V11 now FOLLOW from strict CCW. -/
theorem firstF_three_gaps_positive (P : Fin 11 → XY)
    (hccw : E97A1Index.StrictCCW11 P) :
    0 < actualQuadGap (edgeLength P) 14 ∧
    0 < actualQuadGap (edgeLength P) 288 ∧
    0 < actualQuadGap (edgeLength P) 655 := by
  exact ⟨actual_gap_14_positive P hccw,
    actual_gap_288_positive P hccw,
    actual_gap_655_positive P hccw⟩

/-- Stronger concrete first F closure: no `actualQuadGap > 0` premise.
Still conditional on the four real selected rows, as expected for an
individual leaf. This is NOT the whole 5.2M-node tree theorem. -/
theorem firstF_impossible_from_strict_ccw
    (P : Fin 11 → XY)
    (hccw : E97A1Index.StrictCCW11 P)
    (h1 : E97AllowSound.SelectedRowRealization P 1)
    (h234 : E97AllowSound.SelectedRowRealization P 234)
    (h2099 : E97AllowSound.SelectedRowRealization P 2099)
    (h2226 : E97AllowSound.SelectedRowRealization P 2226) : False := by
  obtain ⟨h14,h288,h655⟩ := firstF_three_gaps_positive P hccw
  exact E97FirstFGeometry10.firstF_geometry_impossible
    P h1 h234 h2099 h2226 h14 h288 h655

#print axioms E97ActualFirstF12.firstF_quad_indices_exact
#print axioms E97ActualFirstF12.firstF_quad_endpoints_exact
#print axioms E97ActualFirstF12.ccw11_quad_strict
#print axioms E97ActualFirstF12.actual_gap_14_positive
#print axioms E97ActualFirstF12.actual_gap_288_positive
#print axioms E97ActualFirstF12.actual_gap_655_positive
#print axioms E97ActualFirstF12.firstF_three_gaps_positive
#print axioms E97ActualFirstF12.firstF_impossible_from_strict_ccw
end E97ActualFirstF12
