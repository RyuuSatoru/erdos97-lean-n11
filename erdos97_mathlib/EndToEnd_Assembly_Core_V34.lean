import Intersection_Geometry_Bridge_V33
import Row_Enumeration_Complete_V15
set_option autoImplicit false
namespace T34EndToEnd
def RootsVerified : Prop := ∀ root : Fin 210, ∃ cert : T33Checker.Certificate,
  T33Checker.checkTree 12 T33Checker.suggestedHints [root.val] cert = true
theorem no_counterexample_of_roots (hmask : T32Table.Certified) (horiented : T33Table.Certified)
    (hroots : RootsVerified) :
    ¬ ∃ P : Fin 11 → E97BlockB.XY, E97A1Index.StrictCCW11 P ∧
      E97RowEnumeration15.HasFourEquidistantAtEveryVertex P := by
  rintro ⟨P,hccw,hfour⟩
  obtain ⟨assignment,hw⟩ := E97RowEnumeration15.geometric_four_gives_assignment P hfour
  have ha := hw 0 (by omega)
  have hr : assignment 0 < 210 := by omega
  obtain ⟨cert,hcheck⟩ := hroots ⟨assignment 0,hr⟩
  have hp : E97TypedChecker15.PrefixRealized P [assignment 0] := by
    intro r hm
    have heq : r = assignment 0 := List.mem_singleton.mp hm
    rw [heq]
    exact ⟨ha.1,ha.2.2⟩
  exact T33Geometry.checked_tree_forbids_assignment hmask horiented P hccw assignment hw
    T33Checker.suggestedHints 12 [assignment 0] cert hp hcheck

theorem vertex_without_four_of_no_counterexample
    (hnone : ¬ ∃ P : Fin 11 → E97BlockB.XY, E97A1Index.StrictCCW11 P ∧
      E97RowEnumeration15.HasFourEquidistantAtEveryVertex P)
    (P : Fin 11 → E97BlockB.XY) (hccw : E97A1Index.StrictCCW11 P) :
    ∃ c : Nat, c < 11 ∧ ∀ w : Finset Nat,
      w.card = 4 → w ⊆ Finset.range 11 → c ∉ w → ¬ E97A3.SelectedRowEq P c w := by
  classical
  by_contra h
  apply hnone
  refine ⟨P,hccw,?_⟩
  intro c hc
  by_contra hn
  apply h
  refine ⟨c,hc,?_⟩
  intro w hcard hbound hexclude heq
  exact hn ⟨w,hcard,hbound,hexclude,heq⟩
#print axioms T34EndToEnd.no_counterexample_of_roots
#print axioms T34EndToEnd.vertex_without_four_of_no_counterexample
end T34EndToEnd
