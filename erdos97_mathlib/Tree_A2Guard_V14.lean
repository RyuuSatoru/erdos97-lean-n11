import E97_RowRealization_Core
import Tree_A2Geometry_V13

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97A2Guard14
open E97BlockB

structure A2Hint where
  rowA : Nat
  rowB : Nat
  rowC : Nat
  witnessU : Nat
  witnessV : Nat
  deriving DecidableEq, Repr

/-- An A2 pruning hint is accepted only for three actual selected centers
sharing the same distinct pair of witnesses. Counts alone are not trusted. -/
def checkedA2 (path : List Nat) (h : A2Hint) : Bool :=
  let a := h.rowA
  let b := h.rowB
  let c := h.rowC
  let u := h.witnessU
  let v := h.witnessV
  decide (a ∈ path ∧ b ∈ path ∧ c ∈ path ∧
    a/210 ≠ b/210 ∧ a/210 ≠ c/210 ∧ b/210 ≠ c/210 ∧
    u < v ∧ v < 11 ∧
    u ∈ E97A2Prefix.rowWitnessSet a ∧ v ∈ E97A2Prefix.rowWitnessSet a ∧
    u ∈ E97A2Prefix.rowWitnessSet b ∧ v ∈ E97A2Prefix.rowWitnessSet b ∧
    u ∈ E97A2Prefix.rowWitnessSet c ∧ v ∈ E97A2Prefix.rowWitnessSet c)

theorem checkedA2_forbids_realization (P : Fin 11 → XY)
    (hccw : E97A1Index.StrictCCW11 P) (path : List Nat)
    (hrows : ∀ p ∈ path, p < 2310 ∧ E97AllowSound.SelectedRowRealization P p)
    (hint : A2Hint) (hcheck : checkedA2 path hint = true) : False := by
  have h := hcheck
  simp only [checkedA2, decide_eq_true_eq] at h
  obtain ⟨ha,hb,hc,hab,hac,hbc,huv,hv,hua,hva,hub,hvb,huc,hvc⟩ := h
  obtain ⟨haBound,haReal⟩ := hrows hint.rowA ha
  obtain ⟨hbBound,hbReal⟩ := hrows hint.rowB hb
  obtain ⟨hcBound,hcReal⟩ := hrows hint.rowC hc
  have hpoints := E97A1Index.ccw11_points_injective P hccw
    hint.witnessU hint.witnessV (by omega) hv (Nat.ne_of_lt huv)
  have hz := E97A2Geometry13.three_bisector_centers_collinear
    (P (Fin.ofNat 11 (hint.rowA/210)))
    (P (Fin.ofNat 11 (hint.rowB/210)))
    (P (Fin.ofNat 11 (hint.rowC/210)))
    (P (Fin.ofNat 11 hint.witnessU)) (P (Fin.ofNat 11 hint.witnessV)) hpoints
    (haReal hint.witnessU hint.witnessV hua hva)
    (hbReal hint.witnessU hint.witnessV hub hvb)
    (hcReal hint.witnessU hint.witnessV huc hvc)
  exact E97A2Geometry13.ccw_no_three_collinear P hccw
    (hint.rowA/210) (hint.rowB/210) (hint.rowC/210)
    (by omega) (by omega) (by omega) hab hac hbc hz

def guardedA2Allows (path : List Nat) (hint : Option A2Hint) : Bool :=
  match hint with
  | none => true
  | some h => !(checkedA2 path h)

/-- Even a malicious hint cannot prune a genuinely realized prefix. -/
theorem realized_prefix_survives_any_A2_hint (P : Fin 11 → XY)
    (hccw : E97A1Index.StrictCCW11 P) (path : List Nat)
    (hrows : ∀ p ∈ path, p < 2310 ∧ E97AllowSound.SelectedRowRealization P p)
    (hint : Option A2Hint) : guardedA2Allows path hint = true := by
  cases hint with
  | none => rfl
  | some hint =>
    cases h : checkedA2 path hint with
    | false => simp [guardedA2Allows,h]
    | true => exact False.elim (checkedA2_forbids_realization P hccw path hrows hint h)

#print axioms E97A2Guard14.checkedA2_forbids_realization
#print axioms E97A2Guard14.realized_prefix_survives_any_A2_hint
end E97A2Guard14
