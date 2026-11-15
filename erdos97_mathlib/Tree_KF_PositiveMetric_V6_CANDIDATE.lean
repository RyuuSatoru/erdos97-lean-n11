import Tree_KF_Coefficient_V4_CANDIDATE

/-!
Erdos 97 v6: bridge arithmetic K0/K2/F certificate checkers to the
real-valued projected evaluations. Crucially, positivity from StrictCCW11
and the interpretation of row union classes as actual equal metric edges
remain separate OPEN geometry obligations. Not a full-tree proof.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97TreeMetricV6
open E97TreeKF4

/-- K0 checked all 55 integer coordinates, not merely a single coordinate. -/
theorem checkedK0_coeff_zero (classes : Array Nat) (q e : Nat)
    (h : checkedK0 classes q = true) (he : e < 55) :
    reducedCoeff classes q e = 0 := by
  have hs := h
  simp only [checkedK0, Bool.and_eq_true] at hs
  have hz := (List.all_eq_true.mp hs.2) e (List.mem_range.mpr he)
  exact decide_eq_true_eq.mp hz

/-- A valid K0 makes every linear evaluation of its 55-vector zero. -/
theorem checkedK0_projected_zero (classes : Array Nat)
    (edgeLength : Nat → ℝ) (q : Nat)
    (h : checkedK0 classes q = true) :
    projectedValue classes edgeLength q = 0 := by
  unfold projectedValue
  apply Finset.sum_eq_zero
  intro e he
  have hc := checkedK0_coeff_zero classes q e h (Finset.mem_range.mp he)
  rw [hc]
  simp

/-- A positive true quadrilateral gap rules out K0. -/
theorem positive_projected_K0_impossible (classes : Array Nat)
    (edgeLength : Nat → ℝ) (q : Nat)
    (h : checkedK0 classes q = true)
    (hpositive : 0 < projectedValue classes edgeLength q) : False := by
  have hz := checkedK0_projected_zero classes edgeLength q h
  linarith

private theorem foldl_coeff_as_sum (classes : Array Nat)
    (ts : List (Nat × Nat)) (e : Nat) (start : Int) :
    ts.foldl (fun acc qw => acc + (Int.ofNat qw.2) *
      reducedCoeff classes qw.1 e) start =
    start + (ts.map (fun qw => (Int.ofNat qw.2) *
      reducedCoeff classes qw.1 e)).sum := by
  induction ts generalizing start with
  | nil => simp
  | cons t rest ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      ring

private theorem cast_weighted_coeff (classes : Array Nat)
    (ts : List (Nat × Nat)) (e : Nat) :
    (((ts.map (fun qw => (Int.ofNat qw.2) *
      reducedCoeff classes qw.1 e)).sum : Int) : ℝ) =
    (ts.map (fun qw => (qw.2 : ℝ) *
      (reducedCoeff classes qw.1 e : ℝ))).sum := by
  induction ts with
  | nil => simp
  | cons t rest ih =>
      simp only [List.map_cons, List.sum_cons, Int.cast_add, Int.cast_mul, ih]
      norm_cast

/-- The REAL weighted sum can be written as a sum of 55 projected
integer coefficients, with the same actual `getQuad` source table. -/
private theorem weighted_projected_exchange (classes : Array Nat)
    (edgeLength : Nat → ℝ) (ts : List (Nat × Nat)) :
    (ts.map (fun qw => (qw.2 : ℝ) *
      projectedValue classes edgeLength qw.1)).sum =
    ∑ e ∈ Finset.range 55,
      (ts.map (fun qw => (qw.2 : ℝ) *
        (reducedCoeff classes qw.1 e : ℝ))).sum * edgeLength e := by
  induction ts with
  | nil => simp
  | cons t rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      unfold projectedValue
      rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e he
      ring

/-- New F bridge: successful integer coefficient balance forces the
positive-weighted sum of REAL projected quadrilateral gaps to be zero. -/
theorem checkedF_projected_weighted_sum_zero (classes : Array Nat)
    (edgeLength : Nat → ℝ) (ts : List (Nat × Nat))
    (h : checkedF classes ts = true) :
    (ts.map (fun qw => (qw.2 : ℝ) *
      projectedValue classes edgeLength qw.1)).sum = 0 := by
  rw [weighted_projected_exchange]
  apply Finset.sum_eq_zero
  intro e he
  have hc := checkedF_coeff_balance classes ts e h (Finset.mem_range.mp he)
  rw [foldl_coeff_as_sum] at hc
  have hzero : (ts.map (fun qw => (Int.ofNat qw.2) *
      reducedCoeff classes qw.1 e)).sum = 0 := by
    simpa using hc
  have hreal := cast_weighted_coeff classes ts e
  rw [hzero] at hreal
  simp only [Int.cast_zero] at hreal
  rw [← hreal]
  simp

/-- A real list with strictly positive entries has positive total. -/
private theorem sum_positive_reals (xs : List ℝ)
    (hne : xs ≠ []) (hpos : ∀ x ∈ xs, 0 < x) : 0 < xs.sum := by
  induction xs with
  | nil => contradiction
  | cons x rest ih =>
      have hx : 0 < x := hpos x (by simp)
      have hr : ∀ y ∈ rest, 0 < y := by
        intro y hy
        exact hpos y (by simp [hy])
      cases rest with
      | nil => simpa using hx
      | cons y ys =>
          have htail : 0 < (y :: ys).sum := ih (by simp) hr
          simpa only [List.sum_cons] using (add_pos hx htail)

/-- Passing F has strictly positive integer weights (and a nonempty list). -/
theorem checkedF_positive_weights (classes : Array Nat)
    (ts : List (Nat × Nat)) (h : checkedF classes ts = true) :
    ts ≠ [] ∧ ∀ qw ∈ ts, 0 < qw.2 := by
  constructor
  · intro hnil
    subst ts
    simp [checkedF] at h
  · intro qw hmem
    have hh := h
    simp only [checkedF, Bool.and_eq_true] at hh
    have ht := (List.all_eq_true.mp hh.1.2) qw hmem
    exact (decide_eq_true_eq.mp ht).2.1

/-- A genuine F witness cannot coexist with strictly positive projected
values for every listed actual quadrilateral. The remaining geometry
obligation is exactly those positivity assumptions. -/
theorem positive_projected_F_impossible (classes : Array Nat)
    (edgeLength : Nat → ℝ) (ts : List (Nat × Nat))
    (h : checkedF classes ts = true)
    (hpos : ∀ qw ∈ ts,
      0 < projectedValue classes edgeLength qw.1) : False := by
  obtain ⟨hne, hweights⟩ := checkedF_positive_weights classes ts h
  have hm : ∀ v ∈ (ts.map (fun qw => (qw.2 : ℝ) *
      projectedValue classes edgeLength qw.1)), 0 < v := by
    intro v hv
    obtain ⟨qw, hq, rfl⟩ := List.mem_map.mp hv
    have hw : (0 : ℝ) < qw.2 := by exact_mod_cast hweights qw hq
    exact mul_pos hw (hpos qw hq)
  have hn : (ts.map (fun qw => (qw.2 : ℝ) *
      projectedValue classes edgeLength qw.1)) ≠ [] := by
    intro hh
    apply hne
    cases ts with
    | nil => rfl
    | cons t ts => simp at hh
  have hpositive := sum_positive_reals _ hn hm
  have hz := checkedF_projected_weighted_sum_zero classes edgeLength ts h
  linarith

/-- The exact first F leaf from record 6901, conditional only on the
unproved geometric positivity of its three true quadrilateral values. -/
theorem first_real_F_contradicts_positive_metric (edgeLength : Nat → ℝ)
    (h14 : 0 < projectedValue firstFClasses edgeLength 14)
    (h288 : 0 < projectedValue firstFClasses edgeLength 288)
    (h655 : 0 < projectedValue firstFClasses edgeLength 655) : False := by
  have hcert := E97TreeKF4.first_real_F_pass
  apply positive_projected_F_impossible firstFClasses edgeLength
    [(14,1),(288,1),(655,1)] hcert
  intro qw hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hq | hq | hq
  · simpa [hq] using h14
  · simpa [hq] using h288
  · simpa [hq] using h655

#print axioms E97TreeMetricV6.checkedK0_coeff_zero
#print axioms E97TreeMetricV6.checkedK0_projected_zero
#print axioms E97TreeMetricV6.positive_projected_K0_impossible
#print axioms E97TreeMetricV6.checkedF_projected_weighted_sum_zero
#print axioms E97TreeMetricV6.checkedF_positive_weights
#print axioms E97TreeMetricV6.positive_projected_F_impossible
#print axioms E97TreeMetricV6.first_real_F_contradicts_positive_metric
end E97TreeMetricV6
