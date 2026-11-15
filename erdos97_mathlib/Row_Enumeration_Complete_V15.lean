import Row_Enumeration_Center00_V15
import Row_Enumeration_Center01_V15
import Row_Enumeration_Center02_V15
import Row_Enumeration_Center03_V15
import Row_Enumeration_Center04_V15
import Row_Enumeration_Center05_V15
import Row_Enumeration_Center06_V15
import Row_Enumeration_Center07_V15
import Row_Enumeration_Center08_V15
import Row_Enumeration_Center09_V15
import Row_Enumeration_Center10_V15
import Tree_TypedChecker_V14

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97RowEnumeration15
open E97BlockB

theorem all_centers_complete (c : Nat) (hc : c < 11) :
    enumeratedWitnessSets c = allFourWitnessSets c := by
  interval_cases c
  · exact center00_complete
  · exact center01_complete
  · exact center02_complete
  · exact center03_complete
  · exact center04_complete
  · exact center05_complete
  · exact center06_complete
  · exact center07_complete
  · exact center08_complete
  · exact center09_complete
  · exact center10_complete

theorem actual_row_covers_any_four (c : Nat) (hc : c < 11) (w : Finset Nat)
    (hcard : w.card = 4) (hbound : w ⊆ Finset.range 11) (hexclude : c ∉ w) :
    ∃ r : Nat, r < 2310 ∧ r/210 = c ∧ E97A2Prefix.rowWitnessSet r = w := by
  have hsub : w ⊆ (Finset.range 11).erase c := by
    intro u hu
    refine Finset.mem_erase.mpr ⟨?_,hbound hu⟩
    intro heq
    subst u
    exact hexclude hu
  have hm : w ∈ allFourWitnessSets c := Finset.mem_powersetCard.mpr ⟨hsub,hcard⟩
  rw [← all_centers_complete c hc] at hm
  simp only [enumeratedWitnessSets, List.mem_toFinset] at hm
  obtain ⟨k,hk,hkw⟩ := List.mem_map.mp hm
  have hk' := List.mem_range.mp hk
  exact ⟨210*c+k,by omega,by omega,hkw⟩

def HasFourEquidistantAtEveryVertex (P : Fin 11 → XY) : Prop :=
  ∀ c : Nat, c < 11 → ∃ w : Finset Nat,
    w.card = 4 ∧ w ⊆ Finset.range 11 ∧ c ∉ w ∧ E97A3.SelectedRowEq P c w

theorem geometric_four_gives_actual_row (P : Fin 11 → XY)
    (hfour : HasFourEquidistantAtEveryVertex P) (c : Nat) (hc : c < 11) :
    ∃ r : Nat, r < 2310 ∧ r/210 = c ∧ E97AllowSound.SelectedRowRealization P r := by
  obtain ⟨w,hcard,hbound,hexclude,hreal⟩ := hfour c hc
  obtain ⟨r,hr,hc',hw⟩ := actual_row_covers_any_four c hc w hcard hbound hexclude
  refine ⟨r,hr,hc',?_⟩
  simpa only [E97AllowSound.SelectedRowRealization,hc',hw] using hreal

theorem geometric_four_gives_assignment (P : Fin 11 → XY)
    (hfour : HasFourEquidistantAtEveryVertex P) :
    ∃ assignment : Nat → Nat, E97TypedChecker14.AssignmentRealized P assignment := by
  classical
  let select : Nat → Nat := fun c =>
    if hc : c < 11 then Classical.choose (geometric_four_gives_actual_row P hfour c hc) else 0
  refine ⟨select,?_⟩
  intro c hc
  have h := Classical.choose_spec (geometric_four_gives_actual_row P hfour c hc)
  simpa only [select,dite_eq_left hc] using h

/-- This is conditional on a literal certificate acceptance theorem.
No full-root acceptance theorem has yet been supplied. -/
theorem checked_certificate_rules_out_counterexample
    (fuel : Nat) (hints : E97TypedChecker14.HintProvider)
    (cert : E97TypedChecker14.Certificate)
    (hcheck : E97TypedChecker14.checkTree fuel hints [] cert = true) :
    ¬ ∃ P : Fin 11 → XY, E97A1Index.StrictCCW11 P ∧
      HasFourEquidistantAtEveryVertex P := by
  rintro ⟨P,hccw,hfour⟩
  obtain ⟨assignment,ha⟩ := geometric_four_gives_assignment P hfour
  exact E97TypedChecker14.checked_root_forbids_assignment fuel hints cert hcheck
    ⟨P,hccw,assignment,ha⟩

#print axioms E97RowEnumeration15.all_centers_complete
#print axioms E97RowEnumeration15.actual_row_covers_any_four
#print axioms E97RowEnumeration15.geometric_four_gives_actual_row
#print axioms E97RowEnumeration15.geometric_four_gives_assignment
#print axioms E97RowEnumeration15.checked_certificate_rules_out_counterexample
end E97RowEnumeration15
