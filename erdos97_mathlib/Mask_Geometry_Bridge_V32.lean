import Thin_Geometry_Bridge_V29
import Mask_Cached_Checker_V32
import Mask_Table_Core_V32
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace T32Geometry
open E97TypedChecker15

theorem validates_original (hcert : T32Table.Certified) (path : List Nat)
    (r : Nat) (hint : T29E97PairGuard15.PairHint)
    (hcheck : T32Checker.checkedPair path r hint = true) :
    E97PairGuard15.checkedPair path r ⟨hint.slot,T28Reason.reasonAt hint.slot⟩ = true := by
  have h := hcheck
  simp only [T32Checker.checkedPair,Bool.and_eq_true,decide_eq_true_eq] at h
  have ha : T32Mask.allowedAt hint.slot = false := by
    cases hm : T32Mask.allowedAt hint.slot <;> simp_all
  obtain ⟨hnz,hvalid⟩ := hcert hint.slot h.1.1 ha
  have hfast : T29E97FastTables19.fastCheckedPair path r ⟨hint.slot,T28Reason.reasonAt hint.slot⟩ = true := by
    simp only [T29E97FastTables19.fastCheckedPair,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨h.1,by simpa only [hvalid,ite_true] using hnz⟩
  rw [E97ThinBridge29.checkedPair_eq] at hfast
  rw [E97FastTables19.fastCheckedPair_eq] at hfast
  exact hfast

theorem pair_survives (hcert : T32Table.Certified) (P : Fin 11 → E97BlockB.XY)
    (hccw : E97A1Index.StrictCCW11 P) (path : List Nat) (r : Nat)
    (hp : ∀ p ∈ path, E97AllowSound.SelectedRowRealization P p)
    (hr : E97AllowSound.SelectedRowRealization P r) (hint : Option T29E97PairGuard15.PairHint) :
    (match hint with | none => true | some h => !(T32Checker.checkedPair path r h)) = true := by
  cases hint with
  | none => rfl
  | some hint =>
    cases h : T32Checker.checkedPair path r hint with
    | false => simp only [h,Bool.not_false]
    | true => exact False.elim (E97PairGuard15.checkedPair_forbids_realization P hccw path r hp hr
        ⟨hint.slot,T28Reason.reasonAt hint.slot⟩ (validates_original hcert path r hint h))

theorem a2Allows_eq (path : List Nat) (hint : Option T29E97A2Guard14.A2Hint) :
    T29E97FastChecker19.guardedA2Allows path hint =
      E97A2Guard14.guardedA2Allows path (hint.map E97ThinBridge29.a2ToOld) := by
  rw [← E97FastChecker19.guardedA2Allows_eq]
  cases hint <;> simp only [T29E97FastChecker19.guardedA2Allows,E97FastChecker19.guardedA2Allows,
    Option.map_none,Option.map_some,E97ThinBridge29.checkedA2_eq]

theorem actual_assignment_row_survives (hcert : T32Table.Certified) (P : Fin 11 → E97BlockB.XY)
    (hccw : E97A1Index.StrictCCW11 P) (assignment : Nat → Nat)
    (hworld : AssignmentRealized P assignment) (hints : T29E97TypedChecker15.HintProvider)
    (path : List Nat) (hp : PrefixRealized P path) (c : Nat) (hc : c < 11) :
    assignment c ∈ T32Checker.candidateRows hints path c := by
  have hr := hworld c hc
  have hall : assignment c ∈ (List.range 210).map (fun k => 210*c+k) := by
    apply List.mem_map.mpr
    refine ⟨assignment c % 210,List.mem_range.mpr (Nat.mod_lt _ (by omega)),?_⟩
    omega
  apply List.mem_filter.mpr
  refine ⟨hall,?_⟩
  have ha2 := E97A2Guard14.realized_prefix_survives_any_A2_hint P hccw (path ++ [assignment c])
    (append_realized P path (assignment c) hp ⟨hr.1,hr.2.2⟩)
    ((hints path (assignment c)).a2.map E97ThinBridge29.a2ToOld)
  have hpair := pair_survives hcert P hccw path (assignment c)
    (by intro p hmem; exact (hp p hmem).2) hr.2.2 (hints path (assignment c)).pair
  simp only [T32Checker.guardedAllows,Bool.and_eq_true]
  exact ⟨hpair,by rw [a2Allows_eq]; exact ha2⟩

theorem checked_tree_forbids_assignment (hcert : T32Table.Certified) (P : Fin 11 → E97BlockB.XY)
    (hccw : E97A1Index.StrictCCW11 P) (assignment : Nat → Nat)
    (hworld : AssignmentRealized P assignment) (hints : T29E97TypedChecker15.HintProvider)
    (fuel : Nat) (path : List Nat) (cert : T32Checker.Certificate)
    (hp : PrefixRealized P path) (hcheck : T32Checker.checkTree fuel hints path cert = true) :
    False := by
  induction fuel generalizing path cert with
  | zero => simp [T32Checker.checkTree] at hcheck
  | succ n ih =>
    cases cert with
    | flow terms receipts =>
      change T29E97EdgeWalk22.checkedFlow path terms receipts = true at hcheck
      rw [E97ThinBridge29.checkedFlow_eq] at hcheck
      exact E97EdgeWalk22.checkedFlow_impossible P hccw path hp terms receipts hcheck
    | empty c =>
      have h := hcheck
      simp only [T32Checker.checkTree, Bool.and_eq_true, decide_eq_true_eq] at h
      have hm := actual_assignment_row_survives hcert P hccw assignment hworld hints path hp c h.1
      rw [h.2] at hm
      simp at hm
    | branch c children =>
      have h := hcheck
      simp only [T32Checker.checkTree, Bool.and_eq_true, decide_eq_true_eq] at h
      have hm := actual_assignment_row_survives hcert P hccw assignment hworld hints path hp c h.1.1
      rw [← h.1.2] at hm
      obtain ⟨⟨r,child⟩,hmem,hr⟩ := List.mem_map.mp hm
      have ht := (List.all_eq_true.mp h.2) (r,child) hmem
      have hw := hworld c h.1.1
      have hrreal : r < 2310 ∧ E97AllowSound.SelectedRowRealization P r := by
        have hr' : r = assignment c := hr
        rw [hr']
        exact ⟨hw.1,hw.2.2⟩
      exact ih (path ++ [r]) child (append_realized P path r hp hrreal) ht

#print axioms T32Geometry.validates_original
#print axioms T32Geometry.actual_assignment_row_survives
#print axioms T32Geometry.checked_tree_forbids_assignment
end T32Geometry
