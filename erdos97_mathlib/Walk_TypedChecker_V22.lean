import Edge_Walk_Flow_V22
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace E97WalkChecker22
open E97TypedChecker15
inductive Certificate where
  | flow (terms : List (Nat × Nat)) (receipts : List E97EdgeWalk22.Receipt)
  | empty (center : Nat)
  | branch (center : Nat) (children : List (Nat × Certificate))
abbrev candidateRows := E97FastChecker19.candidateRows
abbrev suggestedHints := E97FastChecker19.suggestedHints
def checkTree (fuel : Nat) (hints : HintProvider) (path : List Nat)
    (cert : Certificate) : Bool :=
  match fuel with
  | 0 => false
  | n+1 => match cert with
    | .flow terms receipts => E97EdgeWalk22.checkedFlow path terms receipts
    | .empty c => decide (c < 11) && decide (candidateRows hints path c = [])
    | .branch c children => decide (c < 11) &&
        decide (children.map Prod.fst = candidateRows hints path c) &&
        children.all (fun child => checkTree n hints (path ++ [child.1]) child.2)
theorem actual_assignment_row_survives (P : Fin 11 → E97BlockB.XY)
    (hccw : E97A1Index.StrictCCW11 P) (assignment : Nat → Nat)
    (hworld : AssignmentRealized P assignment) (hints : HintProvider)
    (path : List Nat) (hp : PrefixRealized P path) (c : Nat) (hc : c < 11) :
    assignment c ∈ candidateRows hints path c := by
  simpa only [candidateRows,E97FastChecker19.candidateRows_eq] using
    E97TypedChecker15.actual_assignment_row_survives P hccw assignment hworld hints path hp c hc
theorem checked_tree_forbids_assignment (P : Fin 11 → E97BlockB.XY)
    (hccw : E97A1Index.StrictCCW11 P) (assignment : Nat → Nat)
    (hworld : AssignmentRealized P assignment) (hints : HintProvider)
    (fuel : Nat) (path : List Nat) (cert : Certificate)
    (hp : PrefixRealized P path) (hcheck : checkTree fuel hints path cert = true) :
    False := by
  induction fuel generalizing path cert with
  | zero => simp [checkTree] at hcheck
  | succ n ih =>
    cases cert with
    | flow terms receipts =>
      exact E97EdgeWalk22.checkedFlow_impossible P hccw path hp terms receipts hcheck
    | empty c =>
      have h := hcheck
      simp only [checkTree, Bool.and_eq_true, decide_eq_true_eq] at h
      have hm := actual_assignment_row_survives P hccw assignment hworld hints path hp c h.1
      rw [h.2] at hm
      simp at hm
    | branch c children =>
      have h := hcheck
      simp only [checkTree, Bool.and_eq_true, decide_eq_true_eq] at h
      have hm := actual_assignment_row_survives P hccw assignment hworld hints path hp c h.1.1
      rw [← h.1.2] at hm
      obtain ⟨⟨r,child⟩,hmem,hr⟩ := List.mem_map.mp hm
      have ht := (List.all_eq_true.mp h.2) (r,child) hmem
      have hw := hworld c h.1.1
      have hrreal : r < 2310 ∧ E97AllowSound.SelectedRowRealization P r := by
        have hr' : r = assignment c := hr
        rw [hr']
        exact ⟨hw.1,hw.2.2⟩
      exact ih (path ++ [r]) child (append_realized P path r hp hrreal) ht

theorem branch_accept (fuel : Nat) (hints : HintProvider) (path : List Nat)
    (center : Nat) (children : List (Nat × Certificate))
    (hc : center < 11) (hrows : children.map Prod.fst = candidateRows hints path center)
    (hall : children.all (fun ch => checkTree fuel hints (path ++ [ch.1]) ch.2) = true) :
    checkTree (fuel+1) hints path (.branch center children) = true := by
  change (decide (center < 11) && decide (children.map Prod.fst = candidateRows hints path center) &&
    children.all (fun ch => checkTree fuel hints (path ++ [ch.1]) ch.2)) = true
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨hc,hrows⟩,hall⟩
#print axioms E97WalkChecker22.actual_assignment_row_survives
#print axioms E97WalkChecker22.checked_tree_forbids_assignment
#print axioms E97WalkChecker22.branch_accept
end E97WalkChecker22
