import Sparse_TypedChecker_V20
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace E97EdgeWalk22
open E97TreeMetricV8 E97FirstF10
abbrev Receipt := Nat × List (Nat × Nat)

def rowContains (r e : Nat) : Bool :=
  let (a,b,c,d) := E97Packed18.rowAt r
  decide (e = a ∨ e = b ∨ e = c ∨ e = d)

theorem row_contains_equal (L : Nat → ℝ) (r e f : Nat)
    (hrow : RowFourEqual L r) (he : rowContains r e = true) (hf : rowContains r f = true) :
    L e = L f := by
  rcases hr : E97Packed18.rowAt r with ⟨a,b,c,d⟩
  simp only [RowFourEqual,← E97Packed18.rowAt_eq,hr] at hrow
  simp only [rowContains,hr,decide_eq_true_eq] at he hf
  rcases he with rfl | rfl | rfl | rfl <;>
    rcases hf with rfl | rfl | rfl | rfl <;> grind

def checkWalk (path : List Nat) (start finish : Nat) : List (Nat × Nat) → Bool
  | [] => decide (start = finish)
  | (row,next) :: rest =>
    decide (row ∈ path) && rowContains row start && rowContains row next &&
      checkWalk path next finish rest

theorem checkWalk_sound (L : Nat → ℝ) (path : List Nat)
    (hrows : ∀ r ∈ path, RowFourEqual L r)
    (start finish : Nat) (steps : List (Nat × Nat))
    (h : checkWalk path start finish steps = true) : L start = L finish := by
  induction steps generalizing start with
  | nil =>
    simp only [checkWalk,decide_eq_true_eq] at h
    exact congrArg L h
  | cons step rest ih =>
    rcases step with ⟨r,next⟩
    simp only [checkWalk,Bool.and_eq_true,decide_eq_true_eq] at h
    exact (row_contains_equal L r start next (hrows r h.1.1.1) h.1.1.2 h.1.2).trans
      (ih next h.2)

def checkPairings (path : List Nat) : List Nat → List Receipt → Bool
  | [],[] => true
  | e :: es,(f,steps) :: rest =>
    checkWalk path e f steps && checkPairings path es rest
  | _,_ => false

theorem checkPairings_sound (L : Nat → ℝ) (path : List Nat)
    (hrows : ∀ r ∈ path, RowFourEqual L r)
    (es : List Nat) (receipts : List Receipt)
    (h : checkPairings path es receipts = true) :
    (es.map L).sum = ((receipts.map Prod.fst).map L).sum := by
  induction es generalizing receipts with
  | nil =>
    cases receipts with
    | nil => rfl
    | cons r rs => simp only [checkPairings,Bool.false_eq_true] at h
  | cons e es ih =>
    cases receipts with
    | nil => simp only [checkPairings,Bool.false_eq_true] at h
    | cons r rs =>
      rcases r with ⟨f,steps⟩
      simp only [checkPairings,Bool.and_eq_true] at h
      simp only [List.map_cons,List.sum_cons]
      rw [checkWalk_sound L path hrows e f steps h.1,ih rs h.2]

def positiveEdges : List (Nat × Nat) → List Nat
  | [] => []
  | (q,w) :: rest =>
    let (a,b,_,_) := E97Packed18.quadAt q
    List.replicate w a ++ List.replicate w b ++ positiveEdges rest
def negativeEdges : List (Nat × Nat) → List Nat
  | [] => []
  | (q,w) :: rest =>
    let (_,_,c,d) := E97Packed18.quadAt q
    List.replicate w c ++ List.replicate w d ++ negativeEdges rest
def weightedGap (L : Nat → ℝ) (ts : List (Nat × Nat)) : ℝ :=
  (ts.map (fun qw => (qw.2 : ℝ) * actualQuadGap L qw.1)).sum

theorem expanded_gap (L : Nat → ℝ) (ts : List (Nat × Nat)) :
    weightedGap L ts = ((positiveEdges ts).map L).sum - ((negativeEdges ts).map L).sum := by
  induction ts with
  | nil => simp [weightedGap,positiveEdges,negativeEdges]
  | cons qw ts ih =>
    rcases qw with ⟨q,w⟩
    rcases hq : E97Packed18.quadAt q with ⟨a,b,c,d⟩
    have hg : actualQuadGap L q = L a + L b - L c - L d := by
      simp only [actualQuadGap,← E97Packed18.quadAt_eq,hq]
    change (w : ℝ) * actualQuadGap L q + weightedGap L ts = _
    rw [ih,hg]
    simp only [positiveEdges,negativeEdges,hq,List.map_append,List.sum_append,
      List.map_replicate,List.sum_replicate,nsmul_eq_mul]
    ring

def checkedFlow (path : List Nat) (ts : List (Nat × Nat)) (receipts : List Receipt) : Bool :=
  (!ts.isEmpty) &&
  ts.all (fun qw => decide (qw.1 < 660 ∧ 0 < qw.2 ∧ qw.2 ≤ 1000000)) &&
  checkPairings path (positiveEdges ts) receipts &&
  decide (E97Sparse20.sortEdges (receipts.map Prod.fst) = E97Sparse20.sortEdges (negativeEdges ts))

theorem checkedFlow_impossible (P : Fin 11 → E97BlockB.XY)
    (hccw : E97A1Index.StrictCCW11 P) (path : List Nat)
    (hp : E97TypedChecker15.PrefixRealized P path)
    (ts : List (Nat × Nat)) (receipts : List Receipt)
    (hcheck : checkedFlow path ts receipts = true) : False := by
  have h := hcheck
  simp only [checkedFlow,Bool.and_eq_true,decide_eq_true_eq] at h
  have hrows : ∀ r ∈ path, RowFourEqual (E97FirstFGeometry10.edgeLength P) r := by
    intro r hr
    exact E97AllRow13.realized_row_lengths P r (hp r hr).1 (hp r hr).2
  have heq := checkPairings_sound (E97FirstFGeometry10.edgeLength P) path hrows
    (positiveEdges ts) receipts h.1.2
  have hperm : (receipts.map Prod.fst).Perm (negativeEdges ts) := by
    apply (E97Sparse20.sortEdges_perm (receipts.map Prod.fst)).symm.trans
    rw [h.2]
    exact E97Sparse20.sortEdges_perm (negativeEdges ts)
  have hzero : weightedGap (E97FirstFGeometry10.edgeLength P) ts = 0 := by
    rw [expanded_gap,heq,(hperm.map (E97FirstFGeometry10.edgeLength P)).sum_eq,sub_self]
  have hterm : ∀ qw ∈ ts,
      0 < (qw.2 : ℝ) * actualQuadGap (E97FirstFGeometry10.edgeLength P) qw.1 := by
    intro qw hqw
    have hv := decide_eq_true_eq.mp ((List.all_eq_true.mp h.1.1.2) qw hqw)
    exact mul_pos (Nat.cast_pos.mpr hv.2.1)
      (E97AllQuad13.all_actual_quad_gaps_positive P hccw qw.1 hv.1)
  have hpos : 0 < weightedGap (E97FirstFGeometry10.edgeLength P) ts := by
    cases ts with
    | nil => simp at h
    | cons qw rest =>
      change 0 < (qw.2 : ℝ) * actualQuadGap (E97FirstFGeometry10.edgeLength P) qw.1 + _
      apply add_pos_of_pos_of_nonneg (hterm qw List.mem_cons_self)
      apply List.sum_nonneg
      intro x hx
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hx
      exact le_of_lt (hterm r (List.mem_cons_of_mem _ hr))
  linarith

#print axioms E97EdgeWalk22.row_contains_equal
#print axioms E97EdgeWalk22.checkWalk_sound
#print axioms E97EdgeWalk22.checkPairings_sound
#print axioms E97EdgeWalk22.expanded_gap
#print axioms E97EdgeWalk22.checkedFlow_impossible
end E97EdgeWalk22
