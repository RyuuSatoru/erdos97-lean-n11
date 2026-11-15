import Tree_TypedChecker_V15
import RawReason_ASCII_V16
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97HintSearch16
open E97A2Guard14 E97PairGuard15 E97TypedChecker15

def slotOfRows (p r : Nat) : Nat :=
  let a := min (p/210) (r/210)
  let b := max (p/210) (r/210)
  let pairIndex := a*(21-a)/2 + (b-a-1)
  if p/210 < r/210 then pairIndex*44100 + (p%210)*210 + r%210
  else pairIndex*44100 + (r%210)*210 + p%210

/-- These functions produce untrusted suggestions. The typed checker always
validates their row/slot binding and calls guardedReasonAt before pruning. -/
def pairSuggestion (rawReasonAt : Nat → Nat) (path : List Nat) (r : Nat) : Option PairHint :=
  match path with
  | [] => none
  | p :: ps =>
    let slot := slotOfRows p r
    let code := rawReasonAt slot
    if p/210 ≠ r/210 ∧ code ≠ 0 then some ⟨slot,code⟩
    else pairSuggestion rawReasonAt ps r

def witnessPairs (r : Nat) : List (Nat × Nat) :=
  let (a,b,c,d) := E97A2Rows.decodedWitnesses r
  let ws := [a,b,c,d]
  ws.flatMap (fun u => (ws.filter (fun v => u < v)).map (fun v => (u,v)))

def a2FromPairs (path : List Nat) (r : Nat) (pairs : List (Nat × Nat)) : Option A2Hint :=
  match pairs with
  | [] => none
  | (u,v) :: rest =>
    let hits := path.filter (fun p => u ∈ E97A2Prefix.rowWitnessSet p ∧
      v ∈ E97A2Prefix.rowWitnessSet p)
    match hits with
    | a :: b :: _ => some ⟨a,b,r,u,v⟩
    | _ => a2FromPairs path r rest

def suggestedHints (rawReasonAt : Nat → Nat) : HintProvider :=
  fun path r => ⟨a2FromPairs path r (witnessPairs r), pairSuggestion rawReasonAt path r⟩

/-- Safety is inherited for any producer, including the executable search.
This theorem does not assume correctness of the raw U16 bytes. -/
theorem suggestions_keep_actual_row (P : Fin 11 → E97BlockB.XY)
    (hccw : E97A1Index.StrictCCW11 P) (assignment : Nat → Nat)
    (hworld : AssignmentRealized P assignment) (rawReasonAt : Nat → Nat)
    (path : List Nat) (hp : PrefixRealized P path) (c : Nat) (hc : c < 11) :
    assignment c ∈ candidateRows (suggestedHints rawReasonAt) path c := by
  exact actual_assignment_row_survives P hccw assignment hworld
    (suggestedHints rawReasonAt) path hp c hc

#print axioms E97HintSearch16.suggestions_keep_actual_row
end E97HintSearch16
