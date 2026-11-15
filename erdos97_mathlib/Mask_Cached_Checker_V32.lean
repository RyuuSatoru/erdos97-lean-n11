import Certified_Mask_Data_V32
import Thin_List_Proofs_V29
set_option autoImplicit false
namespace T32Checker
open T29E97TypedChecker15
abbrev Certificate := T29E97WalkChecker22.Certificate

def checkedPair (path : List Nat) (nextRow : Nat) (hint : T29E97PairGuard15.PairHint) : Bool :=
  decide (hint.slot < 2425500) &&
  decide (((210 * T29E97FastTables19.fastCenterA hint.slot + T29E97CellSlot.rowX hint.slot) ∈ path ∧
      nextRow = 210 * T29E97FastTables19.fastCenterB hint.slot + T29E97CellSlot.rowY hint.slot) ∨
    ((210 * T29E97FastTables19.fastCenterB hint.slot + T29E97CellSlot.rowY hint.slot) ∈ path ∧
      nextRow = 210 * T29E97FastTables19.fastCenterA hint.slot + T29E97CellSlot.rowX hint.slot)) &&
  !(T32Mask.allowedAt hint.slot)

def pairSuggestion (path : List Nat) (r : Nat) : Option T29E97PairGuard15.PairHint :=
  match path with
  | [] => none
  | p :: ps =>
    let slot := T29E97HintSearch16.slotOfRows p r
    if p/210 ≠ r/210 ∧ T32Mask.allowedAt slot = false then some ⟨slot,0⟩
    else pairSuggestion ps r

def suggestedHints : HintProvider :=
  fun path =>
    let pairs := T29E97FastHint25.prefixPairs (path.map (fun p => (p,T29E97FastHint25.rowMask p)))
    fun r => ⟨T29E97FastHint25.findA2 r (T29E97FastHint25.rowMask r) pairs,pairSuggestion path r⟩

def guardedAllows (path : List Nat) (r : Nat) (hints : CandidateHints) : Bool :=
  (match hints.pair with
    | none => true
    | some h => !(checkedPair path r h)) &&
    T29E97FastChecker19.guardedA2Allows (path ++ [r]) hints.a2

def candidateRows (hints : HintProvider) (path : List Nat) (center : Nat) : List Nat :=
  ((List.range 210).map (fun k => 210*center+k)).filter
    (fun r => guardedAllows path r (hints path r))

def checkTree (fuel : Nat) (hints : HintProvider) (path : List Nat)
    (cert : Certificate) : Bool :=
  match fuel with
  | 0 => false
  | n+1 => match cert with
    | .flow terms receipts => T29E97EdgeWalk22.checkedFlow path terms receipts
    | .empty c => decide (c < 11) && decide (candidateRows hints path c = [])
    | .branch c children => decide (c < 11) &&
        decide (children.map Prod.fst = candidateRows hints path c) &&
        children.all (fun child => checkTree n hints (path ++ [child.1]) child.2)

theorem branch_accept (fuel : Nat) (hints : HintProvider) (path : List Nat)
    (center : Nat) (children : List (Nat × Certificate))
    (hc : center < 11) (hrows : children.map Prod.fst = candidateRows hints path center)
    (hall : children.all (fun ch => checkTree fuel hints (path ++ [ch.1]) ch.2) = true) :
    checkTree (fuel+1) hints path (.branch center children) = true := by
  change (decide (center < 11) && decide (children.map Prod.fst = candidateRows hints path center) &&
    children.all (fun ch => checkTree fuel hints (path ++ [ch.1]) ch.2)) = true
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨hc,hrows⟩,hall⟩
#print axioms T32Checker.branch_accept
end T32Checker
