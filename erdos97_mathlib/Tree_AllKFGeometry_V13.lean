import Tree_ClassInvariant_V13
import Tree_AllQuadGeometry_V13

set_option autoImplicit false
namespace E97AllKF13
open E97BlockB E97ClassInvariant13 E97FirstFGeometry10
open E97TreeKF4 E97TreeMetricV6 E97TreeMetricV8

theorem realized_prefix_projected_positive (P : Fin 11 → XY)
    (hccw : E97A1Index.StrictCCW11 P) (path : List Nat)
    (hrows : ∀ p ∈ path, p < 2310 ∧ E97AllowSound.SelectedRowRealization P p)
    (q : Nat) (hq : q < 660) :
    0 < projectedValue (classesOfRows path) (edgeLength P) q := by
  obtain ⟨hw,hc⟩ := realized_prefix_classes P path hrows
  exact positive_projected_of_actual_gap _ _ q hw.2 hc hq
    (E97AllQuad13.all_actual_quad_gaps_positive P hccw q hq)

/-- Every checked K0 on every geometrically realized prefix is impossible. -/
theorem all_K0_impossible (P : Fin 11 → XY)
    (hccw : E97A1Index.StrictCCW11 P) (path : List Nat)
    (hrows : ∀ p ∈ path, p < 2310 ∧ E97AllowSound.SelectedRowRealization P p)
    (q : Nat) (hcheck : checkedK0 (classesOfRows path) q = true) : False := by
  have h := hcheck
  simp only [checkedK0, Bool.and_eq_true, decide_eq_true_eq] at h
  exact positive_projected_K0_impossible _ _ q hcheck
    (realized_prefix_projected_positive P hccw path hrows q h.1)

/-- Every checked K2 on every geometrically realized prefix is impossible. -/
theorem all_K2_impossible (P : Fin 11 → XY)
    (hccw : E97A1Index.StrictCCW11 P) (path : List Nat)
    (hrows : ∀ p ∈ path, p < 2310 ∧ E97AllowSound.SelectedRowRealization P p)
    (q r : Nat) (hcheck : checkedK2 (classesOfRows path) q r = true) : False := by
  have h := hcheck
  simp only [checkedK2, Bool.and_eq_true, decide_eq_true_eq] at h
  exact positive_projected_K2_impossible _ _ q r hcheck
    (realized_prefix_projected_positive P hccw path hrows q h.1.1.1)
    (realized_prefix_projected_positive P hccw path hrows r h.1.1.2)

/-- Every checked positive F combination on any realized prefix is impossible. -/
theorem all_F_impossible (P : Fin 11 → XY)
    (hccw : E97A1Index.StrictCCW11 P) (path : List Nat)
    (hrows : ∀ p ∈ path, p < 2310 ∧ E97AllowSound.SelectedRowRealization P p)
    (ts : List (Nat × Nat)) (hcheck : checkedF (classesOfRows path) ts = true) :
    False := by
  apply positive_projected_F_impossible _ (edgeLength P) ts hcheck
  intro qw hqw
  have h := hcheck
  simp only [checkedF, Bool.and_eq_true] at h
  have ht := (List.all_eq_true.mp h.1.2) qw hqw
  have hq := (decide_eq_true_eq.mp ht).1
  exact realized_prefix_projected_positive P hccw path hrows qw.1 hq

#print axioms E97AllKF13.realized_prefix_projected_positive
#print axioms E97AllKF13.all_K0_impossible
#print axioms E97AllKF13.all_K2_impossible
#print axioms E97AllKF13.all_F_impossible
end E97AllKF13
