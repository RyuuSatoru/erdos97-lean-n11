import Guarded_LegalCandidate_CANDIDATE
import Tree_A2Guard_V14

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97PairGuard15
open E97BlockB E97CellSlot

structure PairHint where
  slot : Nat
  code : Nat
  deriving DecidableEq, Repr

def checkedPair (path : List Nat) (nextRow : Nat) (hint : PairHint) : Bool :=
  decide (hint.slot < 2425500) &&
  decide (((210 * centerA hint.slot + rowX hint.slot) ∈ path ∧
      nextRow = 210 * centerB hint.slot + rowY hint.slot) ∨
    ((210 * centerB hint.slot + rowY hint.slot) ∈ path ∧
      nextRow = 210 * centerA hint.slot + rowX hint.slot)) &&
  decide (E97Guarded.guardedReasonAt (fun _ => hint.code) hint.slot ≠ 0)

theorem checkedPair_forbids_realization (P : Fin 11 → XY)
    (hccw : E97A1Index.StrictCCW11 P) (path : List Nat) (nextRow : Nat)
    (hp : ∀ p ∈ path, E97AllowSound.SelectedRowRealization P p)
    (hn : E97AllowSound.SelectedRowRealization P nextRow)
    (hint : PairHint) (hcheck : checkedPair path nextRow hint = true) : False := by
  have h := hcheck
  simp only [checkedPair, Bool.and_eq_true, decide_eq_true_eq] at h
  have hlegal := E97Guarded.realized_candidate_survives_guarded_pairwise
    (fun _ => hint.code) P hccw path nextRow hp hn
  exact h.2 (hlegal hint.slot h.1.1 h.1.2)

def guardedPairAllows (path : List Nat) (nextRow : Nat) (hint : Option PairHint) : Bool :=
  match hint with
  | none => true
  | some h => !(checkedPair path nextRow h)

theorem actual_row_survives_pair_hint (P : Fin 11 → XY)
    (hccw : E97A1Index.StrictCCW11 P) (path : List Nat) (nextRow : Nat)
    (hp : ∀ p ∈ path, E97AllowSound.SelectedRowRealization P p)
    (hn : E97AllowSound.SelectedRowRealization P nextRow)
    (hint : Option PairHint) : guardedPairAllows path nextRow hint = true := by
  cases hint with
  | none => rfl
  | some hint =>
    cases h : checkedPair path nextRow hint with
    | false => simp [guardedPairAllows,h]
    | true => exact False.elim (checkedPair_forbids_realization P hccw path nextRow hp hn hint h)

#print axioms E97PairGuard15.checkedPair_forbids_realization
#print axioms E97PairGuard15.actual_row_survives_pair_hint
end E97PairGuard15
