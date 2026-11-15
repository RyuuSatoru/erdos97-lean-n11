import A3_SimilarityGeometry_CANDIDATE
import A1_IndexAlternation_CANDIDATE

/-!
A3 instantiated for FIVE increasing vertex indices within the eleven-point
strict CCW configuration. Other cyclic rotations and the mirrored A3
pattern used by the actual verifier remain follow-on obligations.
CANDIDATE, not yet compiled by Lean.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97A3
open E97BlockB E97A1Index

theorem five_increasing_vertices_A3_impossible
    (P : Fin 11 → XY) (hccw : StrictCCW11 P)
    (ip ia ib ic iq : ℕ)
    (hpa : ip < ia) (hab : ia < ib) (hbc : ib < ic)
    (hcq : ic < iq) (hq : iq < 11)
    (hBP : sqDist (P (Fin.ofNat 11 ib)) (P (Fin.ofNat 11 ip)) =
           sqDist (P (Fin.ofNat 11 ib)) (P (Fin.ofNat 11 ia)))
    (hCQ : sqDist (P (Fin.ofNat 11 ic)) (P (Fin.ofNat 11 iq)) =
           sqDist (P (Fin.ofNat 11 ic)) (P (Fin.ofNat 11 ia)))
    (hCAleCB : sqDist (P (Fin.ofNat 11 ic)) (P (Fin.ofNat 11 ia)) ≤
               sqDist (P (Fin.ofNat 11 ic)) (P (Fin.ofNat 11 ib))) : False := by
  exact five_point_euclidean_impossible
    (P (Fin.ofNat 11 ip)) (P (Fin.ofNat 11 ia))
    (P (Fin.ofNat 11 ib)) (P (Fin.ofNat 11 ic))
    (P (Fin.ofNat 11 iq))
    (hccw ip ia ib hpa hab (by omega))
    (hccw ia ib ic hab hbc (by omega))
    (hccw ia ib iq hab (by omega) hq)
    (hccw ip ia iq hpa (by omega) hq)
    (hccw ia ic iq (by omega) hcq hq)
    (hccw ib ic iq hbc hcq hq)
    hBP hCQ hCAleCB

#print axioms E97A3.five_increasing_vertices_A3_impossible
end E97A3
