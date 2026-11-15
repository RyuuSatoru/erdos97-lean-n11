import Oriented_Mask_Data_V33
set_option autoImplicit false
namespace T33Checker
open T29E97TypedChecker15
inductive Certificate where
  | flow (terms : List (Nat × Nat)) (receipts : List T29E97EdgeWalk22.Receipt)
  | empty (center mask : Nat)
  | branch (center mask : Nat) (children : List (Nat × Certificate))
def suggestedHints : HintProvider :=
  fun path =>
    let pairs := T29E97FastHint25.prefixPairs (path.map (fun p => (p,T29E97FastHint25.rowMask p)))
    fun r => ⟨T29E97FastHint25.findA2 r (T29E97FastHint25.rowMask r) pairs,none⟩
def candidateRows (hints : HintProvider) (path : List Nat) (center mask : Nat) : List Nat :=
  (((List.range 210).filter (fun k => mask.testBit k)).map (fun k => 210*center+k)).filter
    (fun r => T29E97FastChecker19.guardedA2Allows (path ++ [r]) (hints path r).a2)
def checkTree (fuel : Nat) (hints : HintProvider) (path : List Nat) (cert : Certificate) : Bool :=
  match fuel with
  | 0 => false
  | n+1 => match cert with
    | .flow ts rs => T29E97EdgeWalk22.checkedFlow path ts rs
    | .empty c mask => decide (c < 11) && decide (mask = T33Data.pairMask path c) &&
        decide (candidateRows hints path c mask = [])
    | .branch c mask children => decide (c < 11) && decide (mask = T33Data.pairMask path c) &&
        decide (children.map Prod.fst = candidateRows hints path c mask) &&
        children.all (fun ch => checkTree n hints (path ++ [ch.1]) ch.2)
theorem branch_accept (fuel : Nat) (hints : HintProvider) (path : List Nat)
    (center mask : Nat) (children : List (Nat × Certificate)) (hc : center < 11)
    (hm : mask = T33Data.pairMask path center)
    (hr : children.map Prod.fst = candidateRows hints path center mask)
    (hall : children.all (fun ch => checkTree fuel hints (path ++ [ch.1]) ch.2) = true) :
    checkTree (fuel+1) hints path (.branch center mask children) = true := by
  change (decide (center < 11) && decide (mask = T33Data.pairMask path center) &&
    decide (children.map Prod.fst = candidateRows hints path center mask) &&
    children.all (fun ch => checkTree fuel hints (path ++ [ch.1]) ch.2)) = true
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨hc,hm⟩,hr⟩,hall⟩
#print axioms T33Checker.branch_accept
end T33Checker
