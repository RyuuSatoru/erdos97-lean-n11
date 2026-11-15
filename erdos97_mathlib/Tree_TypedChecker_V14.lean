import Tree_AllKFGeometry_V13
import Tree_A2Guard_V14

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97TypedChecker14
open E97BlockB E97ClassInvariant13 E97TreeKF4 E97A2Guard14

abbrev HintProvider := List Nat → Nat → Option A2Hint

inductive Certificate where
  | zero (q : Nat)
  | inverse (q r weightQ weightR : Nat)
  | flow (terms : List (Nat × Nat))
  | empty (center : Nat)
  | branch (center : Nat) (children : List (Nat × Certificate))

def candidateRows (hints : HintProvider) (path : List Nat) (center : Nat) : List Nat :=
  ((List.range 210).map (fun k => 210*center+k)).filter
    (fun r => guardedA2Allows (path ++ [r]) (hints path r))

/-- First concrete typed tree interpreter. It checks every K/F against the
actual coefficient table and branches over every row surviving the sound
A2 hint guard. A1/A3 hint pruning and raw transcript decoding are not yet
implemented here, so the canonical transcript is NOT claimed to pass. -/
def checkTree (fuel : Nat) (hints : HintProvider) (path : List Nat)
    (cert : Certificate) : Bool :=
  match fuel with
  | 0 => false
  | n+1 => match cert with
    | .zero q => checkedK0 (classesOfRows path) q
    | .inverse q r wq wr => checkedF (classesOfRows path) [(q,wq),(r,wr)]
    | .flow terms => checkedF (classesOfRows path) terms
    | .empty c => decide (c < 11) && decide (candidateRows hints path c = [])
    | .branch c children => decide (c < 11) &&
        decide (children.map Prod.fst = candidateRows hints path c) &&
        children.all (fun child => checkTree n hints (path ++ [child.1]) child.2)

def AssignmentRealized (P : Fin 11 → XY) (assignment : Nat → Nat) : Prop :=
  ∀ c, c < 11 → assignment c < 2310 ∧ assignment c / 210 = c ∧
    E97AllowSound.SelectedRowRealization P (assignment c)

def PrefixRealized (P : Fin 11 → XY) (path : List Nat) : Prop :=
  ∀ p ∈ path, p < 2310 ∧ E97AllowSound.SelectedRowRealization P p

theorem append_realized (P : Fin 11 → XY) (path : List Nat) (r : Nat)
    (hp : PrefixRealized P path)
    (hr : r < 2310 ∧ E97AllowSound.SelectedRowRealization P r) :
    PrefixRealized P (path ++ [r]) := by
  intro p hmem
  simp only [List.mem_append, List.mem_singleton] at hmem
  rcases hmem with h | h
  · exact hp p h
  · simpa only [h] using hr

theorem actual_assignment_row_survives (P : Fin 11 → XY)
    (hccw : E97A1Index.StrictCCW11 P) (assignment : Nat → Nat)
    (hworld : AssignmentRealized P assignment) (hints : HintProvider)
    (path : List Nat) (hp : PrefixRealized P path) (c : Nat) (hc : c < 11) :
    assignment c ∈ candidateRows hints path c := by
  have hr := hworld c hc
  have hall : assignment c ∈ (List.range 210).map (fun k => 210*c+k) := by
    apply List.mem_map.mpr
    refine ⟨assignment c % 210,List.mem_range.mpr (Nat.mod_lt _ (by omega)),?_⟩
    omega
  apply List.mem_filter.mpr
  exact ⟨hall,realized_prefix_survives_any_A2_hint P hccw (path ++ [assignment c])
    (append_realized P path (assignment c) hp ⟨hr.1,hr.2.2⟩) (hints path (assignment c))⟩

/-- Acceptance implies a genuine geometric contradiction. No leaf oracle,
A2 budget hypothesis, or externally computed coefficient fact is assumed. -/
theorem checked_tree_forbids_assignment (P : Fin 11 → XY)
    (hccw : E97A1Index.StrictCCW11 P) (assignment : Nat → Nat)
    (hworld : AssignmentRealized P assignment) (hints : HintProvider)
    (fuel : Nat) (path : List Nat) (cert : Certificate)
    (hp : PrefixRealized P path) (hcheck : checkTree fuel hints path cert = true) :
    False := by
  induction fuel generalizing path cert with
  | zero => simp [checkTree] at hcheck
  | succ n ih =>
    cases cert with
    | zero q =>
      exact E97AllKF13.all_K0_impossible P hccw path hp q hcheck
    | inverse q r wq wr =>
      exact E97AllKF13.all_F_impossible P hccw path hp [(q,wq),(r,wr)] hcheck
    | flow terms =>
      exact E97AllKF13.all_F_impossible P hccw path hp terms hcheck
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

theorem checked_root_forbids_assignment (fuel : Nat) (hints : HintProvider)
    (cert : Certificate) (hcheck : checkTree fuel hints [] cert = true) :
    ¬ ∃ P : Fin 11 → XY, E97A1Index.StrictCCW11 P ∧
      ∃ assignment : Nat → Nat, AssignmentRealized P assignment := by
  rintro ⟨P,hccw,assignment,hworld⟩
  exact checked_tree_forbids_assignment P hccw assignment hworld hints fuel [] cert
    (by intro p hp; simp at hp) hcheck

theorem firstF_typed_checker_accepts :
    checkTree 1 (fun _ _ => none) [1,234,2099,2226]
      (.flow [(14,1),(288,1),(655,1)]) = true := by
  change checkedF firstFClasses [(14,1),(288,1),(655,1)] = true
  exact first_real_F_pass

theorem corrupted_firstF_rejected :
    checkTree 1 (fun _ _ => none) [1,234,2099,2226]
      (.flow [(14,1),(288,1),(654,1)]) = false := by
  change checkedF firstFClasses [(14,1),(288,1),(654,1)] = false
  exact forged_real_F_rejected

theorem incomplete_root_rejected :
    checkTree 2 (fun _ _ => none) [] (.branch 0 []) = false := by
  decide +kernel

#print axioms E97TypedChecker14.append_realized
#print axioms E97TypedChecker14.actual_assignment_row_survives
#print axioms E97TypedChecker14.checked_tree_forbids_assignment
#print axioms E97TypedChecker14.checked_root_forbids_assignment
#print axioms E97TypedChecker14.firstF_typed_checker_accepts
#print axioms E97TypedChecker14.corrupted_firstF_rejected
#print axioms E97TypedChecker14.incomplete_root_rejected
end E97TypedChecker14
