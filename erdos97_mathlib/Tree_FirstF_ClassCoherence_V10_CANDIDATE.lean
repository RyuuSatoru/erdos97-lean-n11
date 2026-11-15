import Tree_Quad_Metric_Realization_V8_CANDIDATE

/-!
Erdos #97 v10, first *actual* F leaf: close the finite union-class
coherence gap at its four real selected rows. The generic theorem does
NOT assume CoherentClasses firstFClasses; derives it from exactly four
actual row equalities for 55 abstract real edge lengths.
The geometric realization of these four row equalities and positivity
are treated separately; no theorem here certifies the whole E97TREE.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97FirstF10
open E97TreeKF4 E97TreeMetricV8

/-- The exact four spoke edge values chosen by an actual row are equal. -/
def RowFourEqual (L : Nat → ℝ) (p : Nat) : Prop :=
  let (a,b,c,d) := E97Flow.getRow p
  L a = L b ∧ L a = L c ∧ L a = L d

/-- The four source rows from the FIRST actual F leaf. -/
theorem four_actual_F_rows :
    E97Flow.getRow 1 = (0,1,2,4) ∧
    E97Flow.getRow 234 = (0,10,15,18) ∧
    E97Flow.getRow 2099 = (47,50,52,54) ∧
    E97Flow.getRow 2226 = (18,39,48,54) := by
  decide +kernel

def zeroClass : List Nat := [0,1,2,4,10,15,18,39,47,48,50,52,54]

/-- Independent kernel check of the entire 55-entry union-find state of
 the first real F prefix. All non-singleton vertices are in zeroClass. -/
theorem firstF_class_table :
    (List.range 55).all (fun e =>
      decide (classRep firstFClasses e =
        if e ∈ zeroClass then 0 else e)) = true := by
  decide +kernel

/-- Four row equality facts force exactly the 13 required equalities.
 This is not a restatement of class coherence: only 12 generating
 equalities are assumed and the nontrivial transitive closure is proved. -/
theorem firstF_zero_class_equal (L : Nat → ℝ)
    (r1 : RowFourEqual L 1)
    (r234 : RowFourEqual L 234)
    (r2099 : RowFourEqual L 2099)
    (r2226 : RowFourEqual L 2226) :
    ∀ e, e ∈ zeroClass → L e = L 0 := by
  have h1 : L 0 = L 1 ∧ L 0 = L 2 ∧ L 0 = L 4 := by
    simpa only [RowFourEqual, four_actual_F_rows.1] using r1
  have h2 : L 0 = L 10 ∧ L 0 = L 15 ∧ L 0 = L 18 := by
    simpa only [RowFourEqual, four_actual_F_rows.2.1] using r234
  have h3 : L 47 = L 50 ∧ L 47 = L 52 ∧ L 47 = L 54 := by
    simpa only [RowFourEqual, four_actual_F_rows.2.2.1] using r2099
  have h4 : L 18 = L 39 ∧ L 18 = L 48 ∧ L 18 = L 54 := by
    simpa only [RowFourEqual, four_actual_F_rows.2.2.2] using r2226
  have h54 : L 54 = L 0 := (h4.2.2).symm.trans (h2.2.2).symm
  have h47 : L 47 = L 0 := h3.2.2.trans h54
  have h50 : L 50 = L 0 := h3.1.symm.trans h47
  have h52 : L 52 = L 0 := h3.2.1.symm.trans h47
  intro e he
  have hh : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 4 ∨ e = 10 ∨
      e = 15 ∨ e = 18 ∨ e = 39 ∨ e = 47 ∨ e = 48 ∨
      e = 50 ∨ e = 52 ∨ e = 54 := by
    simpa [zeroClass] using he
  rcases hh with h0 | h1' | h2' | h4' | h10 | h15 | h18 | h39 | h47' | h48 | h50' | h52' | h54'
  · subst e; rfl
  · subst e; exact h1.1.symm
  · subst e; exact h1.2.1.symm
  · subst e; exact h1.2.2.symm
  · subst e; exact h2.1.symm
  · subst e; exact h2.2.1.symm
  · subst e; exact h2.2.2.symm
  · subst e; exact h4.1.symm.trans (h2.2.2).symm
  · subst e; exact h47
  · subst e; exact h4.2.1.symm.trans (h2.2.2).symm
  · subst e; exact h50
  · subst e; exact h52
  · subst e; exact h54

/-- First actual F prefix: row equalities IMPLY CoherentClasses, rather than
 assuming the class invariant as a premise. -/
theorem firstF_coherent_of_four_rows (L : Nat → ℝ)
    (r1 : RowFourEqual L 1)
    (r234 : RowFourEqual L 234)
    (r2099 : RowFourEqual L 2099)
    (r2226 : RowFourEqual L 2226) :
    CoherentClasses firstFClasses L := by
  have hz := firstF_zero_class_equal L r1 r234 r2099 r2226
  intro e he
  have ht := (List.all_eq_true.mp firstF_class_table)
    e (List.mem_range.mpr he)
  have hr : classRep firstFClasses e =
      (if e ∈ zeroClass then 0 else e) := decide_eq_true_eq.mp ht
  rw [hr]
  split_ifs with hm
  · exact hz e hm
  · rfl

/-- The real FIRST F leaf cannot coexist with the four selected row
 equalities and the three STRICT quad-gap inequalities. This drops the
 CoherentClasses assumption from the V9 closing theorem. -/
theorem firstF_impossible_of_four_rows (L : Nat → ℝ)
    (r1 : RowFourEqual L 1)
    (r234 : RowFourEqual L 234)
    (r2099 : RowFourEqual L 2099)
    (r2226 : RowFourEqual L 2226)
    (h14 : 0 < actualQuadGap L 14)
    (h288 : 0 < actualQuadGap L 288)
    (h655 : 0 < actualQuadGap L 655) : False := by
  exact first_F_impossible_of_actual_metric L
    (firstF_coherent_of_four_rows L r1 r234 r2099 r2226)
    h14 h288 h655

/-- A variant with exactly the four canonical row IDs as a membership list. -/
def firstFSelectedRows : List Nat := [1,234,2099,2226]

theorem firstF_impossible_of_all_selected_equal (L : Nat → ℝ)
    (hrows : ∀ p, p ∈ firstFSelectedRows → RowFourEqual L p)
    (h14 : 0 < actualQuadGap L 14)
    (h288 : 0 < actualQuadGap L 288)
    (h655 : 0 < actualQuadGap L 655) : False := by
  apply firstF_impossible_of_four_rows L
    (hrows 1 (by decide)) (hrows 234 (by decide))
    (hrows 2099 (by decide)) (hrows 2226 (by decide))
    h14 h288 h655

/-- The same table must reject a forged representative at edge 10. -/
theorem forged_firstF_rep_rejected :
    (classRep firstFClasses 10 == 10) = false := by
  decide +kernel

#print axioms E97FirstF10.four_actual_F_rows
#print axioms E97FirstF10.firstF_class_table
#print axioms E97FirstF10.firstF_zero_class_equal
#print axioms E97FirstF10.firstF_coherent_of_four_rows
#print axioms E97FirstF10.firstF_impossible_of_four_rows
#print axioms E97FirstF10.firstF_impossible_of_all_selected_equal
#print axioms E97FirstF10.forged_firstF_rep_rejected
end E97FirstF10
