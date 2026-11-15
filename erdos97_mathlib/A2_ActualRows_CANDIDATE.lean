import FlowCheckCore
import Mathlib
/-!
Erdos #97 / A2: independent finite interpretation of the ACTUAL 2310
getRow spoke quadruples, with all 55 edge IDs decoded to 11 endpoints.
This does NOT yet prove the selected-row prefix counts / tree branching.
The only intended large proof is a kernel `by decide` over the real table.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97A2Rows
open E97Flow

/-- Independent lexicographic list of the 55 edges of an 11-gon. -/
def edgeEndpoints : Array (Nat × Nat) := #[
  (0,1),
  (0,2),
  (0,3),
  (0,4),
  (0,5),
  (0,6),
  (0,7),
  (0,8),
  (0,9),
  (0,10),
  (1,2),
  (1,3),
  (1,4),
  (1,5),
  (1,6),
  (1,7),
  (1,8),
  (1,9),
  (1,10),
  (2,3),
  (2,4),
  (2,5),
  (2,6),
  (2,7),
  (2,8),
  (2,9),
  (2,10),
  (3,4),
  (3,5),
  (3,6),
  (3,7),
  (3,8),
  (3,9),
  (3,10),
  (4,5),
  (4,6),
  (4,7),
  (4,8),
  (4,9),
  (4,10),
  (5,6),
  (5,7),
  (5,8),
  (5,9),
  (5,10),
  (6,7),
  (6,8),
  (6,9),
  (6,10),
  (7,8),
  (7,9),
  (7,10),
  (8,9),
  (8,10),
  (9,10)
]

/-- Decode the other endpoint of an edge incident to center; 11 means invalid. -/
def otherEndpoint (center e : Nat) : Nat :=
  let (a,b) := (edgeEndpoints[e]?).getD (11,11)
  if a == center then b else if b == center then a else 11

/-- Four actual witness vertices of the row stored at index p = 210*center+k. -/
def decodedWitnesses (p : Nat) : Nat × Nat × Nat × Nat :=
  let center := p / 210
  let (e0,e1,e2,e3) := getRow p
  (otherEndpoint center e0, otherEndpoint center e1,
   otherEndpoint center e2, otherEndpoint center e3)

/-- Every spoke is in range and incident to the proper center. The four
witness vertices are distinct, in increasing order, and different from center.
Checking these facts also proves that a decoded row has four witnesses. -/
def actualRowOK (p : Nat) : Bool :=
  let center := p / 210
  let (e0,e1,e2,e3) := getRow p
  let (a,b,d,e) := decodedWitnesses p
  decide (p < 2310 ∧ center < 11 ∧
    e0 < 55 ∧ e1 < 55 ∧ e2 < 55 ∧ e3 < 55 ∧
    a < b ∧ b < d ∧ d < e ∧ e < 11 ∧
    a ≠ center ∧ b ≠ center ∧ d ≠ center ∧ e ≠ center)

/-- Closed finite assertion about all 11×210 rows, using exactly E97Flow.getRow.
It does not assume that a producer, C++ checker, or a Python script is sound. -/
theorem all_actual_rows_valid :
    (List.range 2310).all actualRowOK = true := by
  decide

#print axioms E97A2Rows.all_actual_rows_valid
end E97A2Rows
