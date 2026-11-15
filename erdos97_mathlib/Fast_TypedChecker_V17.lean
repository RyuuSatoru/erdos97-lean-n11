import Fast_Lookup_V17
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace E97FastChecker17
open E97TypedChecker15 E97ClassInvariant13 E97TreeKF4 E97A2Guard14

def guardedAllows (path : List Nat) (r : Nat) (hints : CandidateHints) : Bool :=
  guardedA2Allows (path ++ [r]) hints.a2 &&
    (match hints.pair with
    | none => true
    | some h => !(E97FastLookup17.fastCheckedPair path r h))

theorem guardedAllows_eq (path : List Nat) (r : Nat) (hints : CandidateHints) :
    guardedAllows path r hints = E97TypedChecker15.guardedAllows path r hints := by
  cases h : hints.pair <;>
    simp only [guardedAllows,E97TypedChecker15.guardedAllows,h,
      E97PairGuard15.guardedPairAllows,E97FastLookup17.fastCheckedPair_eq]

def candidateRows (hints : HintProvider) (path : List Nat) (center : Nat) : List Nat :=
  ((List.range 210).map (fun k => 210*center+k)).filter
    (fun r => guardedAllows path r (hints path r))

theorem candidateRows_eq (hints : HintProvider) (path : List Nat) (c : Nat) :
    candidateRows hints path c = E97TypedChecker15.candidateRows hints path c := by
  simp only [candidateRows,guardedAllows_eq,E97TypedChecker15.candidateRows]

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

theorem checkTree_eq (fuel : Nat) (hints : HintProvider) (path : List Nat)
    (cert : Certificate) :
    checkTree fuel hints path cert = E97TypedChecker15.checkTree fuel hints path cert := by
  induction fuel generalizing path cert with
  | zero => rfl
  | succ n ih =>
    cases cert <;>
      simp only [checkTree,E97TypedChecker15.checkTree,candidateRows_eq,ih]

theorem checked_tree_forbids_assignment (P : Fin 11 → E97BlockB.XY)
    (hccw : E97A1Index.StrictCCW11 P) (assignment : Nat → Nat)
    (hworld : AssignmentRealized P assignment) (hints : HintProvider)
    (fuel : Nat) (path : List Nat) (cert : Certificate)
    (hp : PrefixRealized P path) (hcheck : checkTree fuel hints path cert = true) :
    False := by
  exact E97TypedChecker15.checked_tree_forbids_assignment P hccw assignment hworld
    hints fuel path cert hp (by simpa only [checkTree_eq] using hcheck)

#print axioms E97FastChecker17.guardedAllows_eq
#print axioms E97FastChecker17.candidateRows_eq
#print axioms E97FastChecker17.checkTree_eq
#print axioms E97FastChecker17.checked_tree_forbids_assignment
end E97FastChecker17
