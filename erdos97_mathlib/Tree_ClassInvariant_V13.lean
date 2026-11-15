import Tree_AllRowGeometry_V13

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97ClassInvariant13
open E97TreeKF4 E97TreeMetricV8 E97FirstF10 E97FirstFGeometry10

def WellFormed (cs : Array Nat) : Prop :=
  cs.size = 55 ∧ ∀ e, e < 55 → classRep cs e < 55

theorem empty_wellFormed : WellFormed emptyClasses := by
  constructor
  · decide +kernel
  · intro e he
    simp [classRep, emptyClasses, he]

theorem empty_coherent (L : Nat → ℝ) : CoherentClasses emptyClasses L := by
  intro e he
  simp [classRep, emptyClasses, he]

theorem merge_lookup (cs : Array Nat) (a b e : Nat) (he : e < cs.size) :
    classRep (mergeClasses cs a b) e =
      if classRep cs e == max (classRep cs a) (classRep cs b)
      then min (classRep cs a) (classRep cs b) else classRep cs e := by
  simp [classRep, mergeClasses, he]

theorem merge_wellFormed (cs : Array Nat) (a b : Nat)
    (hw : WellFormed cs) (ha : a < 55) (_hb : b < 55) :
    WellFormed (mergeClasses cs a b) := by
  constructor
  · simpa [mergeClasses] using hw.1
  · intro e he
    rw [merge_lookup cs a b e (by simpa [hw.1] using he)]
    split_ifs
    · exact lt_of_le_of_lt (min_le_left _ _) (hw.2 a ha)
    · exact hw.2 e he

/-- A true equality merges two representative classes without losing semantics. -/
theorem merge_coherent (cs : Array Nat) (L : Nat → ℝ) (a b : Nat)
    (hw : WellFormed cs) (hc : CoherentClasses cs L)
    (ha : a < 55) (hb : b < 55) (hab : L a = L b) :
    CoherentClasses (mergeClasses cs a b) L := by
  have hr : L (classRep cs a) = L (classRep cs b) :=
    (hc a ha).symm.trans (hab.trans (hc b hb))
  have hminmax : L (max (classRep cs a) (classRep cs b)) =
      L (min (classRep cs a) (classRep cs b)) := by
    rcases le_total (classRep cs a) (classRep cs b) with h | h
    · simpa [max_eq_right h, min_eq_left h] using hr.symm
    · simpa [max_eq_left h, min_eq_right h] using hr
  intro e he
  rw [merge_lookup cs a b e (by simpa [hw.1] using he)]
  split_ifs with hm
  · have hrep : classRep cs e = max (classRep cs a) (classRep cs b) := by
      simpa only [beq_iff_eq] using hm
    apply (hc e he).trans
    rw [hrep]
    exact hminmax
  · exact hc e he

theorem row_edges_bounded (p : Nat) (hp : p < 2310) :
    let (a,b,c,d) := E97Flow.getRow p
    a < 55 ∧ b < 55 ∧ c < 55 ∧ d < 55 := by
  have h := E97A2Prefix.actual_row_ok_of_lt p hp
  simp only [E97A2Rows.actualRowOK, decide_eq_true_eq] at h
  exact ⟨h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1⟩

theorem addActualRow_preserves (cs : Array Nat) (L : Nat → ℝ) (p : Nat)
    (hw : WellFormed cs) (hc : CoherentClasses cs L)
    (hp : p < 2310) (hr : RowFourEqual L p) :
    WellFormed (addActualRow cs p) ∧ CoherentClasses (addActualRow cs p) L := by
  have hbounds := row_edges_bounded p hp
  rcases hh : E97Flow.getRow p with ⟨a,b,c,d⟩
  simp only [hh] at hbounds
  simp only [RowFourEqual, hh] at hr
  obtain ⟨ha,hb,hc',hd⟩ := hbounds
  have hw1 := merge_wellFormed cs a b hw ha hb
  have hl1 := merge_coherent cs L a b hw hc ha hb hr.1
  have hw2 := merge_wellFormed (mergeClasses cs a b) a c hw1 ha hc'
  have hl2 := merge_coherent (mergeClasses cs a b) L a c hw1 hl1 ha hc' hr.2.1
  have hw3 := merge_wellFormed (mergeClasses (mergeClasses cs a b) a c) a d hw2 ha hd
  have hl3 := merge_coherent (mergeClasses (mergeClasses cs a b) a c) L a d hw2 hl2 ha hd hr.2.2
  simpa only [addActualRow, hh] using And.intro hw3 hl3

def classesOfRows (path : List Nat) : Array Nat :=
  path.foldl addActualRow emptyClasses

theorem fold_preserves (path : List Nat) (cs : Array Nat) (L : Nat → ℝ)
    (hw : WellFormed cs) (hc : CoherentClasses cs L)
    (hrows : ∀ p ∈ path, p < 2310 ∧ RowFourEqual L p) :
    WellFormed (path.foldl addActualRow cs) ∧
      CoherentClasses (path.foldl addActualRow cs) L := by
  induction path generalizing cs with
  | nil => exact ⟨hw,hc⟩
  | cons p ps ih =>
    have hp := hrows p (by simp)
    obtain ⟨hw',hc'⟩ := addActualRow_preserves cs L p hw hc hp.1 hp.2
    exact ih _ hw' hc' (by intro r hr; exact hrows r (by simp [hr]))

/-- Arbitrary realized prefixes give a bounded and coherent actual union state. -/
theorem realized_prefix_classes (P : Fin 11 → E97BlockB.XY) (path : List Nat)
    (hrows : ∀ p ∈ path, p < 2310 ∧ E97AllowSound.SelectedRowRealization P p) :
    WellFormed (classesOfRows path) ∧
      CoherentClasses (classesOfRows path) (edgeLength P) := by
  apply fold_preserves path emptyClasses (edgeLength P)
    empty_wellFormed (empty_coherent (edgeLength P))
  intro p hp
  have h := hrows p hp
  exact ⟨h.1,E97AllRow13.realized_row_lengths P p h.1 h.2⟩

#print axioms E97ClassInvariant13.empty_wellFormed
#print axioms E97ClassInvariant13.empty_coherent
#print axioms E97ClassInvariant13.merge_lookup
#print axioms E97ClassInvariant13.merge_wellFormed
#print axioms E97ClassInvariant13.merge_coherent
#print axioms E97ClassInvariant13.row_edges_bounded
#print axioms E97ClassInvariant13.addActualRow_preserves
#print axioms E97ClassInvariant13.fold_preserves
#print axioms E97ClassInvariant13.realized_prefix_classes
end E97ClassInvariant13
