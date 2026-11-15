import E97_RowRealization_Core
import A3_CyclicMirror_CANDIDATE

/-!
Erdos #97 A3: derive both forbidden C++ row-pair patterns from
selected-row equal-distance conditions. This does NOT yet prove that
`getRow`/bitmask predicates of the certificate parser supply the listed
witnesses: that is a separate finite-combinatorial parser obligation.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace E97A3
open E97BlockB

/- A chosen row centered at `center` has one common squared distance
for every two vertices named by its witness set. -/
/-- C++ pattern 1: B-row contains P,A and C-row contains Q,A,B. -/
theorem selected_rows_forbid_BC
    (P : Fin 11 → XY)
    (ip ia ib ic iq : Nat)
    (h : FiveCCW (P (Fin.ofNat 11 ip)) (P (Fin.ofNat 11 ia))
      (P (Fin.ofNat 11 ib)) (P (Fin.ofNat 11 ic))
      (P (Fin.ofNat 11 iq)))
    (wB wC : Finset Nat)
    (hB : SelectedRowEq P ib wB) (hC : SelectedRowEq P ic wC)
    (hPB : ip ∈ wB) (hAB : ia ∈ wB)
    (hQC : iq ∈ wC) (hAC : ia ∈ wC) (hBC : ib ∈ wC) : False := by
  exact fiveCCW_forbids_pattern_BC
    (P (Fin.ofNat 11 ip)) (P (Fin.ofNat 11 ia))
    (P (Fin.ofNat 11 ib)) (P (Fin.ofNat 11 ic))
    (P (Fin.ofNat 11 iq)) h
    (hB ip ia hPB hAB)
    (hC iq ia hQC hAC)
    (hC ia ib hAC hBC)

/-- C++ mirror pattern 2: A-row contains P,B,C and B-row contains Q,C. -/
theorem selected_rows_forbid_AB
    (P : Fin 11 → XY)
    (ip ia ib ic iq : Nat)
    (h : FiveCCW (P (Fin.ofNat 11 ip)) (P (Fin.ofNat 11 ia))
      (P (Fin.ofNat 11 ib)) (P (Fin.ofNat 11 ic))
      (P (Fin.ofNat 11 iq)))
    (wA wB : Finset Nat)
    (hA : SelectedRowEq P ia wA) (hB : SelectedRowEq P ib wB)
    (hPA : ip ∈ wA) (hBA : ib ∈ wA) (hCA : ic ∈ wA)
    (hQB : iq ∈ wB) (hCB : ic ∈ wB) : False := by
  exact fiveCCW_forbids_pattern_AB
    (P (Fin.ofNat 11 ip)) (P (Fin.ofNat 11 ia))
    (P (Fin.ofNat 11 ib)) (P (Fin.ofNat 11 ic))
    (P (Fin.ofNat 11 iq)) h
    (hA ip ic hPA hCA)
    (hA ic ib hCA hBA)
    (hB iq ic hQB hCB)

#print axioms E97A3.selected_rows_forbid_BC
#print axioms E97A3.selected_rows_forbid_AB
end E97A3
