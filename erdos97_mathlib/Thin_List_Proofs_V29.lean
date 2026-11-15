import Thin_Certificate_Quote_V29
set_option autoImplicit false
namespace T29ListProof

theorem all_cons {α : Type} {p : α → Bool} {x : α} {xs : List α}
    (hx : p x = true) (hxs : xs.all p = true) : (x :: xs).all p = true := by
  change (p x && xs.all p) = true
  rw [hx,hxs]
  rfl

theorem all_nil {α : Type} {p : α → Bool} : ([] : List α).all p = true := rfl

#print axioms T29ListProof.all_cons
#print axioms T29ListProof.all_nil
end T29ListProof

namespace T29E97WalkChecker22
open T29E97TypedChecker15
theorem branch_accept (fuel : Nat) (hints : HintProvider) (path : List Nat)
    (center : Nat) (children : List (Nat × Certificate))
    (hc : center < 11) (hrows : children.map Prod.fst = candidateRows hints path center)
    (hall : children.all (fun ch => checkTree fuel hints (path ++ [ch.1]) ch.2) = true) :
    checkTree (fuel+1) hints path (.branch center children) = true := by
  change (decide (center < 11) && decide (children.map Prod.fst = candidateRows hints path center) &&
    children.all (fun ch => checkTree fuel hints (path ++ [ch.1]) ch.2)) = true
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨hc,hrows⟩,hall⟩
#print axioms T29E97WalkChecker22.branch_accept
end T29E97WalkChecker22
