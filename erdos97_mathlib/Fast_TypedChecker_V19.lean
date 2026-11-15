import Fast_Tables_V19
import Packed_Hints_V18
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace E97FastChecker19
open E97TypedChecker15 E97A2Guard14
def rowWitnessSet (p : Nat) : Finset Nat :=
  let (a,b,c,d) := E97FastTables19.decodedWitnesses p
  {a,b,c,d}
theorem rowWitnessSet_eq (p : Nat) : rowWitnessSet p = E97A2Prefix.rowWitnessSet p := by
  simp only [rowWitnessSet,E97FastTables19.decodedWitnesses_eq,E97A2Prefix.rowWitnessSet]
def checkedA2 (path : List Nat) (h : A2Hint) : Bool :=
  let a := h.rowA
  let b := h.rowB
  let c := h.rowC
  let u := h.witnessU
  let v := h.witnessV
  decide (a ∈ path ∧ b ∈ path ∧ c ∈ path ∧
    a/210 ≠ b/210 ∧ a/210 ≠ c/210 ∧ b/210 ≠ c/210 ∧
    u < v ∧ v < 11 ∧
    u ∈ rowWitnessSet a ∧ v ∈ rowWitnessSet a ∧
    u ∈ rowWitnessSet b ∧ v ∈ rowWitnessSet b ∧
    u ∈ rowWitnessSet c ∧ v ∈ rowWitnessSet c)

theorem checkedA2_eq (p : List Nat) (h : A2Hint) :
    checkedA2 p h = E97A2Guard14.checkedA2 p h := by
  simp only [checkedA2,rowWitnessSet_eq,E97A2Guard14.checkedA2]
def guardedA2Allows (path : List Nat) (hint : Option A2Hint) : Bool :=
  match hint with
  | none => true
  | some h => !(checkedA2 path h)
theorem guardedA2Allows_eq (p : List Nat) (h : Option A2Hint) :
    guardedA2Allows p h = E97A2Guard14.guardedA2Allows p h := by
  cases h <;> simp only [guardedA2Allows,E97A2Guard14.guardedA2Allows,checkedA2_eq]
def witnessPairs (r : Nat) : List (Nat × Nat) :=
  let (a,b,c,d) := E97FastTables19.decodedWitnesses r
  let ws := [a,b,c,d]
  ws.flatMap (fun u => (ws.filter (fun v => u < v)).map (fun v => (u,v)))

def a2FromPairs (path : List Nat) (r : Nat) (pairs : List (Nat × Nat)) : Option A2Hint :=
  match pairs with
  | [] => none
  | (u,v) :: rest =>
    let hits := path.filter (fun p => u ∈ rowWitnessSet p ∧
      v ∈ rowWitnessSet p)
    match hits with
    | a :: b :: _ => some ⟨a,b,r,u,v⟩
    | _ => a2FromPairs path r rest

def suggestedHints (rawReasonAt : Nat → Nat) : HintProvider :=
  fun path r => ⟨a2FromPairs path r (witnessPairs r), E97HintSearch16.pairSuggestion rawReasonAt path r⟩

def guardedAllows (path : List Nat) (r : Nat) (hints : CandidateHints) : Bool :=
  (match hints.pair with
    | none => true
    | some h => !(E97FastTables19.fastCheckedPair path r h)) &&
    E97FastChecker19.guardedA2Allows (path ++ [r]) hints.a2

theorem guardedAllows_eq (path : List Nat) (r : Nat) (hints : CandidateHints) :
    guardedAllows path r hints = E97TypedChecker15.guardedAllows path r hints := by
  cases h : hints.pair <;>
    simp only [guardedAllows,E97TypedChecker15.guardedAllows,h,
      E97PairGuard15.guardedPairAllows,E97FastTables19.fastCheckedPair_eq,guardedA2Allows_eq,Bool.and_comm]

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
    | .zero q => E97Packed18.checkedK0 (E97Packed18.classesOfRows path) q
    | .inverse q r wq wr => E97Packed18.checkedF (E97Packed18.classesOfRows path) [(q,wq),(r,wr)]
    | .flow terms => E97Packed18.checkedF (E97Packed18.classesOfRows path) terms
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
      simp only [checkTree,E97TypedChecker15.checkTree,candidateRows_eq,ih,E97Packed18.checkedK0_eq,E97Packed18.checkedF_eq,E97Packed18.classesOfRows_eq]

theorem checked_tree_forbids_assignment (P : Fin 11 → E97BlockB.XY)
    (hccw : E97A1Index.StrictCCW11 P) (assignment : Nat → Nat)
    (hworld : AssignmentRealized P assignment) (hints : HintProvider)
    (fuel : Nat) (path : List Nat) (cert : Certificate)
    (hp : PrefixRealized P path) (hcheck : checkTree fuel hints path cert = true) :
    False := by
  exact E97TypedChecker15.checked_tree_forbids_assignment P hccw assignment hworld
    hints fuel path cert hp (by simpa only [checkTree_eq] using hcheck)

#print axioms E97FastChecker19.rowWitnessSet_eq
#print axioms E97FastChecker19.checkedA2_eq
#print axioms E97FastChecker19.guardedA2Allows_eq
#print axioms E97FastChecker19.guardedAllows_eq
#print axioms E97FastChecker19.candidateRows_eq
#print axioms E97FastChecker19.checkTree_eq
#print axioms E97FastChecker19.checked_tree_forbids_assignment
end E97FastChecker19
