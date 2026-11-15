import BE_MaskToWitness_CANDIDATE
/-!
A row from the actual 2310-row table never contains its own center.
The first theorem is a single finite kernel check, independent of the Allow U16 table.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97A1CenterExclusion
open E97A2Prefix

def rowCenterExcluded (p : Nat) : Bool :=
  decide (p / 210 ∉ rowWitnessSet p)

/-- This is a finite computation over the original 2310 real getRow rows. -/
theorem all_row_centers_excluded :
    (List.range 2310).all rowCenterExcluded = true := by decide

/-- A member of any actual row is not its center. -/
theorem witness_ne_center (p u : Nat)
    (hp : p < 2310) (hu : u ∈ rowWitnessSet p) : u ≠ p / 210 := by
  have hs : rowCenterExcluded p = true :=
    (List.all_eq_true.mp all_row_centers_excluded) p (List.mem_range.mpr hp)
  have hno : p / 210 ∉ rowWitnessSet p := by
    simpa only [rowCenterExcluded, decide_eq_true_eq] using hs
  intro heq
  apply hno
  simpa [heq] using hu

#print axioms E97A1CenterExclusion.all_row_centers_excluded
#print axioms E97A1CenterExclusion.witness_ne_center
end E97A1CenterExclusion
