import Tree_FirstF_ClassCoherence_V10_CANDIDATE
import E97_RowRealization_Core

/-!
V10 geometrical pilot: derive four row metric equalities from the actual
SelectedRowRealization on the XY coordinates, using actual getRow and the
55-edge endpoint table. This does NOT yet derive STRICT quadrilateral
inequalities from StrictCCW11 or certify all F leaf records.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97FirstFGeometry10
open E97FirstF10 E97BlockB E97TreeMetricV8 E97AllowSound

/-- The actual squared Euclidean distance of an unordered E97 edge. -/
def edgeSquare (P : Fin 11 → XY) (e : Nat) : ℝ :=
  let (a,b) := (E97A2Rows.edgeEndpoints[e]?).getD (0,0)
  sqDist (P (Fin.ofNat 11 a)) (P (Fin.ofNat 11 b))

/-- The actual (nonnegative) Euclidean edge length. -/
noncomputable def edgeLength (P : Fin 11 → XY) (e : Nat) : ℝ :=
  Real.sqrt (edgeSquare P e)

theorem sqDist_symm (a b : XY) : sqDist a b = sqDist b a := by
  dsimp [sqDist]
  ring

/-- Applying square root preserves each row's three equalities. -/
theorem row_four_sqrt (L : Nat → ℝ) (p : Nat)
    (h : RowFourEqual L p) :
    RowFourEqual (fun e => Real.sqrt (L e)) p := by
  rcases hh : E97Flow.getRow p with ⟨a,b,c,d⟩
  simp only [RowFourEqual, hh] at h ⊢
  exact ⟨congrArg Real.sqrt h.1,
    congrArg Real.sqrt h.2.1, congrArg Real.sqrt h.2.2⟩

/-- SelectedRowRealization at REAL row 1 entails all four
 actual squared-distance spoke edge equalities. -/
theorem firstF_actual_row_1_square (P : Fin 11 → XY)
    (h : SelectedRowRealization P 1) :
    RowFourEqual (edgeSquare P) 1 := by
  have hs : E97A3.SelectedRowEq P 0 (E97A2Prefix.rowWitnessSet 1) := by
    simpa only [SelectedRowRealization] using h
  change edgeSquare P 0 = edgeSquare P 1 ∧
    edgeSquare P 0 = edgeSquare P 2 ∧
    edgeSquare P 0 = edgeSquare P 4
  constructor
  · calc
      edgeSquare P 0 = sqDist (P (Fin.ofNat 11 0)) (P (Fin.ofNat 11 1)) := by
        change sqDist (P (Fin.ofNat 11 0)) (P (Fin.ofNat 11 1)) =
          sqDist (P (Fin.ofNat 11 0)) (P (Fin.ofNat 11 1))
        rfl
      _ = sqDist (P (Fin.ofNat 11 0)) (P (Fin.ofNat 11 2)) :=
        hs 1 2 (by decide +kernel) (by decide +kernel)
      _ = edgeSquare P 1 := by
        change sqDist (P (Fin.ofNat 11 0)) (P (Fin.ofNat 11 2)) =
          sqDist (P (Fin.ofNat 11 0)) (P (Fin.ofNat 11 2))
        rfl
  constructor
  · calc
      edgeSquare P 0 = sqDist (P (Fin.ofNat 11 0)) (P (Fin.ofNat 11 1)) := by
        change sqDist (P (Fin.ofNat 11 0)) (P (Fin.ofNat 11 1)) =
          sqDist (P (Fin.ofNat 11 0)) (P (Fin.ofNat 11 1))
        rfl
      _ = sqDist (P (Fin.ofNat 11 0)) (P (Fin.ofNat 11 3)) :=
        hs 1 3 (by decide +kernel) (by decide +kernel)
      _ = edgeSquare P 2 := by
        change sqDist (P (Fin.ofNat 11 0)) (P (Fin.ofNat 11 3)) =
          sqDist (P (Fin.ofNat 11 0)) (P (Fin.ofNat 11 3))
        rfl
  · calc
      edgeSquare P 0 = sqDist (P (Fin.ofNat 11 0)) (P (Fin.ofNat 11 1)) := by
        change sqDist (P (Fin.ofNat 11 0)) (P (Fin.ofNat 11 1)) =
          sqDist (P (Fin.ofNat 11 0)) (P (Fin.ofNat 11 1))
        rfl
      _ = sqDist (P (Fin.ofNat 11 0)) (P (Fin.ofNat 11 5)) :=
        hs 1 5 (by decide +kernel) (by decide +kernel)
      _ = edgeSquare P 4 := by
        change sqDist (P (Fin.ofNat 11 0)) (P (Fin.ofNat 11 5)) =
          sqDist (P (Fin.ofNat 11 0)) (P (Fin.ofNat 11 5))
        rfl

/-- SelectedRowRealization at REAL row 234 entails all four
 actual squared-distance spoke edge equalities. -/
theorem firstF_actual_row_234_square (P : Fin 11 → XY)
    (h : SelectedRowRealization P 234) :
    RowFourEqual (edgeSquare P) 234 := by
  have hs : E97A3.SelectedRowEq P 1 (E97A2Prefix.rowWitnessSet 234) := by
    simpa only [SelectedRowRealization] using h
  change edgeSquare P 0 = edgeSquare P 10 ∧
    edgeSquare P 0 = edgeSquare P 15 ∧
    edgeSquare P 0 = edgeSquare P 18
  constructor
  · calc
      edgeSquare P 0 = sqDist (P (Fin.ofNat 11 1)) (P (Fin.ofNat 11 0)) := by
        change sqDist (P (Fin.ofNat 11 0)) (P (Fin.ofNat 11 1)) =
          sqDist (P (Fin.ofNat 11 1)) (P (Fin.ofNat 11 0))
        exact sqDist_symm (P (Fin.ofNat 11 0)) (P (Fin.ofNat 11 1))
      _ = sqDist (P (Fin.ofNat 11 1)) (P (Fin.ofNat 11 2)) :=
        hs 0 2 (by decide +kernel) (by decide +kernel)
      _ = edgeSquare P 10 := by
        change sqDist (P (Fin.ofNat 11 1)) (P (Fin.ofNat 11 2)) =
          sqDist (P (Fin.ofNat 11 1)) (P (Fin.ofNat 11 2))
        rfl
  constructor
  · calc
      edgeSquare P 0 = sqDist (P (Fin.ofNat 11 1)) (P (Fin.ofNat 11 0)) := by
        change sqDist (P (Fin.ofNat 11 0)) (P (Fin.ofNat 11 1)) =
          sqDist (P (Fin.ofNat 11 1)) (P (Fin.ofNat 11 0))
        exact sqDist_symm (P (Fin.ofNat 11 0)) (P (Fin.ofNat 11 1))
      _ = sqDist (P (Fin.ofNat 11 1)) (P (Fin.ofNat 11 7)) :=
        hs 0 7 (by decide +kernel) (by decide +kernel)
      _ = edgeSquare P 15 := by
        change sqDist (P (Fin.ofNat 11 1)) (P (Fin.ofNat 11 7)) =
          sqDist (P (Fin.ofNat 11 1)) (P (Fin.ofNat 11 7))
        rfl
  · calc
      edgeSquare P 0 = sqDist (P (Fin.ofNat 11 1)) (P (Fin.ofNat 11 0)) := by
        change sqDist (P (Fin.ofNat 11 0)) (P (Fin.ofNat 11 1)) =
          sqDist (P (Fin.ofNat 11 1)) (P (Fin.ofNat 11 0))
        exact sqDist_symm (P (Fin.ofNat 11 0)) (P (Fin.ofNat 11 1))
      _ = sqDist (P (Fin.ofNat 11 1)) (P (Fin.ofNat 11 10)) :=
        hs 0 10 (by decide +kernel) (by decide +kernel)
      _ = edgeSquare P 18 := by
        change sqDist (P (Fin.ofNat 11 1)) (P (Fin.ofNat 11 10)) =
          sqDist (P (Fin.ofNat 11 1)) (P (Fin.ofNat 11 10))
        rfl

/-- SelectedRowRealization at REAL row 2099 entails all four
 actual squared-distance spoke edge equalities. -/
theorem firstF_actual_row_2099_square (P : Fin 11 → XY)
    (h : SelectedRowRealization P 2099) :
    RowFourEqual (edgeSquare P) 2099 := by
  have hs : E97A3.SelectedRowEq P 9 (E97A2Prefix.rowWitnessSet 2099) := by
    simpa only [SelectedRowRealization] using h
  change edgeSquare P 47 = edgeSquare P 50 ∧
    edgeSquare P 47 = edgeSquare P 52 ∧
    edgeSquare P 47 = edgeSquare P 54
  constructor
  · calc
      edgeSquare P 47 = sqDist (P (Fin.ofNat 11 9)) (P (Fin.ofNat 11 6)) := by
        change sqDist (P (Fin.ofNat 11 6)) (P (Fin.ofNat 11 9)) =
          sqDist (P (Fin.ofNat 11 9)) (P (Fin.ofNat 11 6))
        exact sqDist_symm (P (Fin.ofNat 11 6)) (P (Fin.ofNat 11 9))
      _ = sqDist (P (Fin.ofNat 11 9)) (P (Fin.ofNat 11 7)) :=
        hs 6 7 (by decide +kernel) (by decide +kernel)
      _ = edgeSquare P 50 := by
        change sqDist (P (Fin.ofNat 11 9)) (P (Fin.ofNat 11 7)) =
          sqDist (P (Fin.ofNat 11 7)) (P (Fin.ofNat 11 9))
        exact (sqDist_symm (P (Fin.ofNat 11 7)) (P (Fin.ofNat 11 9))).symm
  constructor
  · calc
      edgeSquare P 47 = sqDist (P (Fin.ofNat 11 9)) (P (Fin.ofNat 11 6)) := by
        change sqDist (P (Fin.ofNat 11 6)) (P (Fin.ofNat 11 9)) =
          sqDist (P (Fin.ofNat 11 9)) (P (Fin.ofNat 11 6))
        exact sqDist_symm (P (Fin.ofNat 11 6)) (P (Fin.ofNat 11 9))
      _ = sqDist (P (Fin.ofNat 11 9)) (P (Fin.ofNat 11 8)) :=
        hs 6 8 (by decide +kernel) (by decide +kernel)
      _ = edgeSquare P 52 := by
        change sqDist (P (Fin.ofNat 11 9)) (P (Fin.ofNat 11 8)) =
          sqDist (P (Fin.ofNat 11 8)) (P (Fin.ofNat 11 9))
        exact (sqDist_symm (P (Fin.ofNat 11 8)) (P (Fin.ofNat 11 9))).symm
  · calc
      edgeSquare P 47 = sqDist (P (Fin.ofNat 11 9)) (P (Fin.ofNat 11 6)) := by
        change sqDist (P (Fin.ofNat 11 6)) (P (Fin.ofNat 11 9)) =
          sqDist (P (Fin.ofNat 11 9)) (P (Fin.ofNat 11 6))
        exact sqDist_symm (P (Fin.ofNat 11 6)) (P (Fin.ofNat 11 9))
      _ = sqDist (P (Fin.ofNat 11 9)) (P (Fin.ofNat 11 10)) :=
        hs 6 10 (by decide +kernel) (by decide +kernel)
      _ = edgeSquare P 54 := by
        change sqDist (P (Fin.ofNat 11 9)) (P (Fin.ofNat 11 10)) =
          sqDist (P (Fin.ofNat 11 9)) (P (Fin.ofNat 11 10))
        rfl

/-- SelectedRowRealization at REAL row 2226 entails all four
 actual squared-distance spoke edge equalities. -/
theorem firstF_actual_row_2226_square (P : Fin 11 → XY)
    (h : SelectedRowRealization P 2226) :
    RowFourEqual (edgeSquare P) 2226 := by
  have hs : E97A3.SelectedRowEq P 10 (E97A2Prefix.rowWitnessSet 2226) := by
    simpa only [SelectedRowRealization] using h
  change edgeSquare P 18 = edgeSquare P 39 ∧
    edgeSquare P 18 = edgeSquare P 48 ∧
    edgeSquare P 18 = edgeSquare P 54
  constructor
  · calc
      edgeSquare P 18 = sqDist (P (Fin.ofNat 11 10)) (P (Fin.ofNat 11 1)) := by
        change sqDist (P (Fin.ofNat 11 1)) (P (Fin.ofNat 11 10)) =
          sqDist (P (Fin.ofNat 11 10)) (P (Fin.ofNat 11 1))
        exact sqDist_symm (P (Fin.ofNat 11 1)) (P (Fin.ofNat 11 10))
      _ = sqDist (P (Fin.ofNat 11 10)) (P (Fin.ofNat 11 4)) :=
        hs 1 4 (by decide +kernel) (by decide +kernel)
      _ = edgeSquare P 39 := by
        change sqDist (P (Fin.ofNat 11 10)) (P (Fin.ofNat 11 4)) =
          sqDist (P (Fin.ofNat 11 4)) (P (Fin.ofNat 11 10))
        exact (sqDist_symm (P (Fin.ofNat 11 4)) (P (Fin.ofNat 11 10))).symm
  constructor
  · calc
      edgeSquare P 18 = sqDist (P (Fin.ofNat 11 10)) (P (Fin.ofNat 11 1)) := by
        change sqDist (P (Fin.ofNat 11 1)) (P (Fin.ofNat 11 10)) =
          sqDist (P (Fin.ofNat 11 10)) (P (Fin.ofNat 11 1))
        exact sqDist_symm (P (Fin.ofNat 11 1)) (P (Fin.ofNat 11 10))
      _ = sqDist (P (Fin.ofNat 11 10)) (P (Fin.ofNat 11 6)) :=
        hs 1 6 (by decide +kernel) (by decide +kernel)
      _ = edgeSquare P 48 := by
        change sqDist (P (Fin.ofNat 11 10)) (P (Fin.ofNat 11 6)) =
          sqDist (P (Fin.ofNat 11 6)) (P (Fin.ofNat 11 10))
        exact (sqDist_symm (P (Fin.ofNat 11 6)) (P (Fin.ofNat 11 10))).symm
  · calc
      edgeSquare P 18 = sqDist (P (Fin.ofNat 11 10)) (P (Fin.ofNat 11 1)) := by
        change sqDist (P (Fin.ofNat 11 1)) (P (Fin.ofNat 11 10)) =
          sqDist (P (Fin.ofNat 11 10)) (P (Fin.ofNat 11 1))
        exact sqDist_symm (P (Fin.ofNat 11 1)) (P (Fin.ofNat 11 10))
      _ = sqDist (P (Fin.ofNat 11 10)) (P (Fin.ofNat 11 9)) :=
        hs 1 9 (by decide +kernel) (by decide +kernel)
      _ = edgeSquare P 54 := by
        change sqDist (P (Fin.ofNat 11 10)) (P (Fin.ofNat 11 9)) =
          sqDist (P (Fin.ofNat 11 9)) (P (Fin.ofNat 11 10))
        exact (sqDist_symm (P (Fin.ofNat 11 9)) (P (Fin.ofNat 11 10))).symm

/-- The same four real selected rows also force the row-length
 equalities used by the union-class bridge. -/
theorem firstF_geometry_row_equalities (P : Fin 11 → XY)
    (h1 : SelectedRowRealization P 1)
    (h234 : SelectedRowRealization P 234)
    (h2099 : SelectedRowRealization P 2099)
    (h2226 : SelectedRowRealization P 2226) :
    RowFourEqual (edgeLength P) 1 ∧
    RowFourEqual (edgeLength P) 234 ∧
    RowFourEqual (edgeLength P) 2099 ∧
    RowFourEqual (edgeLength P) 2226 := by
  exact ⟨row_four_sqrt (edgeSquare P) 1 (firstF_actual_row_1_square P h1),
    row_four_sqrt (edgeSquare P) 234 (firstF_actual_row_234_square P h234),
    row_four_sqrt (edgeSquare P) 2099 (firstF_actual_row_2099_square P h2099),
    row_four_sqrt (edgeSquare P) 2226 (firstF_actual_row_2226_square P h2226)⟩

/-- This is the significant metric closure improvement: for the concrete
 first F leaf, CoherentClasses now follows from four real selected rows;
 it is no longer supplied as a standalone axiom or premise. -/
theorem firstF_geometry_coherent (P : Fin 11 → XY)
    (h1 : SelectedRowRealization P 1)
    (h234 : SelectedRowRealization P 234)
    (h2099 : SelectedRowRealization P 2099)
    (h2226 : SelectedRowRealization P 2226) :
    CoherentClasses E97TreeKF4.firstFClasses (edgeLength P) := by
  obtain ⟨r1,r234,r2099,r2226⟩ :=
    firstF_geometry_row_equalities P h1 h234 h2099 h2226
  exact firstF_coherent_of_four_rows (edgeLength P)
    r1 r234 r2099 r2226

/-- The first F cannot coexist with four ACTUAL row realizations and three
 strict quad inequalities on actual Euclidean edge lengths. StrictCCW11 ->
 those three inequalities remains a separate OPEN geometric task. -/
theorem firstF_geometry_impossible (P : Fin 11 → XY)
    (h1 : SelectedRowRealization P 1)
    (h234 : SelectedRowRealization P 234)
    (h2099 : SelectedRowRealization P 2099)
    (h2226 : SelectedRowRealization P 2226)
    (h14 : 0 < actualQuadGap (edgeLength P) 14)
    (h288 : 0 < actualQuadGap (edgeLength P) 288)
    (h655 : 0 < actualQuadGap (edgeLength P) 655) : False := by
  exact E97TreeMetricV8.first_F_impossible_of_actual_metric (edgeLength P)
    (firstF_geometry_coherent P h1 h234 h2099 h2226) h14 h288 h655

#print axioms E97FirstFGeometry10.sqDist_symm
#print axioms E97FirstFGeometry10.row_four_sqrt
#print axioms E97FirstFGeometry10.firstF_actual_row_1_square
#print axioms E97FirstFGeometry10.firstF_actual_row_234_square
#print axioms E97FirstFGeometry10.firstF_actual_row_2099_square
#print axioms E97FirstFGeometry10.firstF_actual_row_2226_square
#print axioms E97FirstFGeometry10.firstF_geometry_row_equalities
#print axioms E97FirstFGeometry10.firstF_geometry_coherent
#print axioms E97FirstFGeometry10.firstF_geometry_impossible
end E97FirstFGeometry10
