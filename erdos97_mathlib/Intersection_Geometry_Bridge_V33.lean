import Mask_Geometry_Bridge_V32
import Mask_Intersection_Checker_V33
import Oriented_Mask_Core_V33
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace T33Geometry
open E97TypedChecker15

theorem actual_pair_bit (hcert : T32Table.Certified) (horiented : T33Table.Certified)
    (P : Fin 11 → E97BlockB.XY) (hccw : E97A1Index.StrictCCW11 P)
    (p : Nat) (hp : p < 2310 ∧ E97AllowSound.SelectedRowRealization P p)
    (c k : Nat) (hc : c < 11) (hk : k < 210)
    (hr : E97AllowSound.SelectedRowRealization P (210*c+k)) :
    (T33Data.rowMask p c).testBit k = true := by
  cases hbit : (T33Data.rowMask p c).testBit k with
  | true => rfl
  | false =>
    have hcheck := horiented p hp.1 c hc k hk hbit
    have hsafe := T32Geometry.pair_survives hcert P hccw [p] (210*c+k)
      (by intro q hq; have heq : q = p := List.mem_singleton.mp hq; simpa only [heq] using hp.2)
      hr (some ⟨T29E97HintSearch16.slotOfRows p (210*c+k),0⟩)
    simpa only [hcheck,Bool.not_true] using hsafe

theorem actual_intersection_bit (hcert : T32Table.Certified) (horiented : T33Table.Certified)
    (P : Fin 11 → E97BlockB.XY) (hccw : E97A1Index.StrictCCW11 P)
    (path : List Nat) (hp : PrefixRealized P path) (c k : Nat) (hc : c < 11) (hk : k < 210)
    (hr : E97AllowSound.SelectedRowRealization P (210*c+k)) :
    (T33Data.pairMask path c).testBit k = true := by
  induction path with
  | nil => simp only [T33Data.pairMask,List.foldr_nil,Nat.testBit_two_pow_sub_one,decide_eq_true_eq]; exact hk
  | cons p ps ih =>
    have hfirst := actual_pair_bit hcert horiented P hccw p (hp p (by simp)) c k hc hk hr
    have hrest := ih (by intro q hq; exact hp q (by simp only [List.mem_cons]; exact Or.inr hq))
    change (T33Data.rowMask p c &&& T33Data.pairMask ps c).testBit k = true
    rw [Nat.testBit_and,hfirst,hrest]
    rfl

theorem actual_assignment_row_survives (hcert : T32Table.Certified) (horiented : T33Table.Certified)
    (P : Fin 11 → E97BlockB.XY) (hccw : E97A1Index.StrictCCW11 P) (assignment : Nat → Nat)
    (hworld : AssignmentRealized P assignment) (hints : T29E97TypedChecker15.HintProvider)
    (path : List Nat) (hp : PrefixRealized P path) (c mask : Nat) (hc : c < 11)
    (hm : mask = T33Data.pairMask path c) :
    assignment c ∈ T33Checker.candidateRows hints path c mask := by
  have hr := hworld c hc
  let k := assignment c % 210
  have hk : k < 210 := Nat.mod_lt _ (by omega)
  have heq : 210*c+k = assignment c := by dsimp [k]; omega
  have hreal : E97AllowSound.SelectedRowRealization P (210*c+k) := by rw [heq]; exact hr.2.2
  have hbit := actual_intersection_bit hcert horiented P hccw path hp c k hc hk hreal
  have hmemb : assignment c ∈ ((List.range 210).filter (fun j => mask.testBit j)).map (fun j => 210*c+j) := by
    apply List.mem_map.mpr
    refine ⟨k,List.mem_filter.mpr ⟨List.mem_range.mpr hk,?_⟩,heq⟩
    rw [hm]
    exact hbit
  apply List.mem_filter.mpr
  refine ⟨hmemb,?_⟩
  rw [T32Geometry.a2Allows_eq]
  exact E97A2Guard14.realized_prefix_survives_any_A2_hint P hccw (path ++ [assignment c])
    (append_realized P path (assignment c) hp ⟨hr.1,hr.2.2⟩)
    ((hints path (assignment c)).a2.map E97ThinBridge29.a2ToOld)

theorem checked_tree_forbids_assignment (hcert : T32Table.Certified) (horiented : T33Table.Certified)
    (P : Fin 11 → E97BlockB.XY) (hccw : E97A1Index.StrictCCW11 P) (assignment : Nat → Nat)
    (hworld : AssignmentRealized P assignment) (hints : T29E97TypedChecker15.HintProvider)
    (fuel : Nat) (path : List Nat) (cert : T33Checker.Certificate)
    (hp : PrefixRealized P path) (hcheck : T33Checker.checkTree fuel hints path cert = true) : False := by
  induction fuel generalizing path cert with
  | zero => simp [T33Checker.checkTree] at hcheck
  | succ n ih =>
    cases cert with
    | flow ts rs =>
      change T29E97EdgeWalk22.checkedFlow path ts rs = true at hcheck
      rw [E97ThinBridge29.checkedFlow_eq] at hcheck
      exact E97EdgeWalk22.checkedFlow_impossible P hccw path hp ts rs hcheck
    | empty c mask =>
      have h := hcheck
      simp only [T33Checker.checkTree,Bool.and_eq_true,decide_eq_true_eq] at h
      have hm := actual_assignment_row_survives hcert horiented P hccw assignment hworld hints path hp c mask h.1.1 h.1.2
      rw [h.2] at hm
      simp at hm
    | branch c mask children =>
      have h := hcheck
      simp only [T33Checker.checkTree,Bool.and_eq_true,decide_eq_true_eq] at h
      have hm := actual_assignment_row_survives hcert horiented P hccw assignment hworld hints path hp c mask h.1.1.1 h.1.1.2
      rw [← h.1.2] at hm
      obtain ⟨⟨r,child⟩,hmem,hr⟩ := List.mem_map.mp hm
      have ht := (List.all_eq_true.mp h.2) (r,child) hmem
      have hw := hworld c h.1.1.1
      have hrreal : r < 2310 ∧ E97AllowSound.SelectedRowRealization P r := by
        have hr' : r = assignment c := hr
        rw [hr']
        exact ⟨hw.1,hw.2.2⟩
      exact ih (path ++ [r]) child (append_realized P path r hp hrreal) ht
#print axioms T33Geometry.actual_pair_bit
#print axioms T33Geometry.actual_intersection_bit
#print axioms T33Geometry.actual_assignment_row_survives
#print axioms T33Geometry.checked_tree_forbids_assignment
end T33Geometry
