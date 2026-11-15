import A3_RotatedVertices_Distinct_CANDIDATE
import CheckReason_A3_Sound_CANDIDATE
/-!
This *removes* the explicit FiveCCW, hpattern, and vertex-validity hypotheses
from both BC/AB soundness transports. The remaining hcell is a genuine open
obligation: tying the slot to the correct row/center pair (and the reverse
center ordering case) is NOT yet discharged by this module.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97A3Pattern
open E97AllowFinite E97A3Index E97Bitmask E97AllowSound E97BlockB E97A3

/-- Vertex numbered j in the decoded five-point cyclic tuple of a code. -/
def vertex (code j : Nat) : Nat :=
  rot5 ((code - 56) / 10) (((code - 56) % 10) / 2) j

/-- A3 BC code cannot occur for two realized selected rows when its
actual cell centers and row IDs are BC in that order. -/
theorem A3_BC_checked_geometry_from_code
    (P : Fin 11 → XY) (hccw : E97A1Index.StrictCCW11 P)
    (slot code x y : Nat)
    (hs : slot < 2425500)
    (hlo : 55 < code) (hhi : code ≤ 4675)
    (heven : (code - 56) % 2 = 0)
    (hcell : cellData slot =
      (vertex code 2, vertex code 3, x, y,
       rowMask (vertex code 2) x, rowMask (vertex code 3) y))
    (hx : x < 210) (hy : y < 210)
    (hB : SelectedRowRealization P (210 * vertex code 2 + x))
    (hC : SelectedRowRealization P (210 * vertex code 3 + y))
    (hcheck : checkReason slot code = true) : False := by
  obtain ⟨hp, ha, hb, hc, hq, hpa, hqa, hqb, hab,
          _hpb, _hpc, _hbc, _hqc⟩ := code_vertices_valid code hlo hhi
  have hpattern : patternAt (code - 56) =
      ⟨vertex code 2, vertex code 3,
       twoBits (vertex code 0) (vertex code 1),
       threeBits (vertex code 4) (vertex code 1) (vertex code 2)⟩ := by
    simpa only [vertex] using patternAt_bc (code - 56) heven
  have hfive : FiveCCW
      (P (Fin.ofNat 11 (vertex code 0)))
      (P (Fin.ofNat 11 (vertex code 1)))
      (P (Fin.ofNat 11 (vertex code 2)))
      (P (Fin.ofNat 11 (vertex code 3)))
      (P (Fin.ofNat 11 (vertex code 4))) := by
    simpa only [vertex] using code_five_ccw P hccw code hlo hhi
  exact E97CheckReason.A3_BC_checked_forbids_realization P
    slot code (vertex code 0) (vertex code 1) (vertex code 2)
      (vertex code 3) (vertex code 4) x y
    hs hlo hhi hcell hpattern hx hy
    hp ha hb hc hq hpa hqa hqb hab
    hfive hB hC hcheck

/-- Reflected AB code cannot occur for the matching two selected rows,
again without assuming independent FiveCCW or decoded pattern equality. -/
theorem A3_AB_checked_geometry_from_code
    (P : Fin 11 → XY) (hccw : E97A1Index.StrictCCW11 P)
    (slot code x y : Nat)
    (hs : slot < 2425500)
    (hlo : 55 < code) (hhi : code ≤ 4675)
    (hodd : (code - 56) % 2 ≠ 0)
    (hcell : cellData slot =
      (vertex code 1, vertex code 2, x, y,
       rowMask (vertex code 1) x, rowMask (vertex code 2) y))
    (hx : x < 210) (hy : y < 210)
    (hA : SelectedRowRealization P (210 * vertex code 1 + x))
    (hB : SelectedRowRealization P (210 * vertex code 2 + y))
    (hcheck : checkReason slot code = true) : False := by
  obtain ⟨hp, ha, hb, hc, hq, _hpa, _hqa, _hqb, _hab,
          hpb, hpc, hbc, hqc⟩ := code_vertices_valid code hlo hhi
  have hpattern : patternAt (code - 56) =
      ⟨vertex code 1, vertex code 2,
       threeBits (vertex code 0) (vertex code 2) (vertex code 3),
       twoBits (vertex code 4) (vertex code 3)⟩ := by
    simpa only [vertex] using patternAt_ab (code - 56) hodd
  have hfive : FiveCCW
      (P (Fin.ofNat 11 (vertex code 0)))
      (P (Fin.ofNat 11 (vertex code 1)))
      (P (Fin.ofNat 11 (vertex code 2)))
      (P (Fin.ofNat 11 (vertex code 3)))
      (P (Fin.ofNat 11 (vertex code 4))) := by
    simpa only [vertex] using code_five_ccw P hccw code hlo hhi
  exact E97CheckReason.A3_AB_checked_forbids_realization P
    slot code (vertex code 0) (vertex code 1) (vertex code 2)
      (vertex code 3) (vertex code 4) x y
    hs hlo hhi hcell hpattern hx hy
    hp ha hb hc hq hpb hpc hbc hqc
    hfive hA hB hcheck

#print axioms E97A3Pattern.A3_BC_checked_geometry_from_code
#print axioms E97A3Pattern.A3_AB_checked_geometry_from_code
end E97A3Pattern
