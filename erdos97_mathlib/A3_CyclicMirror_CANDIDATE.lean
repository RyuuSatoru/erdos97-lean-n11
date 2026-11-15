import A3_OrderedFiveVertices_CANDIDATE

/-!
Erdos #97 A3: the FIVE cyclic orientations and the reflected pattern.
This file is new and remains CANDIDATE until Lean kernel compilation.
No new axioms, no sorry. Squared Euclidean distance is used throughout.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97A3
open E97BlockB E97A1Index

/-- Reflection in the x-axis. It reverses orientation and preserves sqDist. -/
def reflectY (z : XY) : XY := (z.1, -z.2)

theorem reflectY_sqDist (x y : XY) :
    sqDist (reflectY x) (reflectY y) = sqDist x y := by
  dsimp [reflectY, sqDist]
  ring

theorem reflectY_orient (x y z : XY) :
    orient (reflectY x) (reflectY y) (reflectY z) =
      -orient x y z := by
  dsimp [reflectY, orient]
  ring

theorem orient_reverse (x y z : XY) :
    orient x y z = -orient z y x := by
  dsimp [orient]
  ring

theorem orient_rotate (x y z : XY) :
    orient x y z = orient y z x := by
  dsimp [orient]
  ring

theorem reflectY_reverse_positive (x y z : XY)
    (h : 0 < orient z y x) :
    0 < orient (reflectY x) (reflectY y) (reflectY z) := by
  rw [reflectY_orient, orient_reverse]
  linarith

/-- Every triple among p,a,b,c,q in their cyclic five-point order
has positive orientation. Ten triples suffice and are not arbitrary axioms:
they follow from strict convexity of the 11-gon below. -/
structure FiveCCW (p a b c q : XY) : Prop where
  pab : 0 < orient p a b
  pac : 0 < orient p a c
  paq : 0 < orient p a q
  pbc : 0 < orient p b c
  pbq : 0 < orient p b q
  pcq : 0 < orient p c q
  abc : 0 < orient a b c
  abq : 0 < orient a b q
  acq : 0 < orient a c q
  bcq : 0 < orient b c q

/-- Cyclic rotation preserves the ten orientation inequalities. -/
theorem FiveCCW.rotate {p a b c q : XY} (h : FiveCCW p a b c q) :
    FiveCCW a b c q p := by
  refine {
    pab := h.abc
    pac := h.abq
    paq := ?_
    pbc := h.acq
    pbq := ?_
    pcq := ?_
    abc := h.bcq
    abq := ?_
    acq := ?_
    bcq := ?_
  }
  · rw [← orient_rotate p a b]
    exact h.pab
  · rw [← orient_rotate p a c]
    exact h.pac
  · rw [← orient_rotate p a q]
    exact h.paq
  · rw [← orient_rotate p b c]
    exact h.pbc
  · rw [← orient_rotate p b q]
    exact h.pbq
  · rw [← orient_rotate p c q]
    exact h.pcq

/-- One statement supplies exactly the five rotations enumerated in the C++
`for (t=0; t<5; ++t)` loop. No reflection assumption is needed here. -/
theorem FiveCCW.five_rotations {p a b c q : XY}
    (h : FiveCCW p a b c q) :
    FiveCCW p a b c q ∧
    FiveCCW a b c q p ∧
    FiveCCW b c q p a ∧
    FiveCCW c q p a b ∧
    FiveCCW q p a b c := by
  have h1 := h.rotate
  have h2 := h1.rotate
  have h3 := h2.rotate
  have h4 := h3.rotate
  exact ⟨h, h1, h2, h3, h4⟩

/-- The 10 CCW orientations for an increasing five-subset of the 11-gon. -/
theorem FiveCCW.of_increasing
    (P : Fin 11 → XY) (hccw : StrictCCW11 P)
    (ip ia ib ic iq : ℕ)
    (hpa : ip < ia) (hab : ia < ib) (hbc : ib < ic)
    (hcq : ic < iq) (hq : iq < 11) :
    FiveCCW (P (Fin.ofNat 11 ip)) (P (Fin.ofNat 11 ia))
      (P (Fin.ofNat 11 ib)) (P (Fin.ofNat 11 ic))
      (P (Fin.ofNat 11 iq)) := by
  refine {
    pab := hccw ip ia ib hpa hab (by omega)
    pac := hccw ip ia ic hpa (by omega) (by omega)
    paq := hccw ip ia iq hpa (by omega) hq
    pbc := hccw ip ib ic (by omega) hbc (by omega)
    pbq := hccw ip ib iq (by omega) (by omega) hq
    pcq := hccw ip ic iq (by omega) hcq hq
    abc := hccw ia ib ic hab hbc (by omega)
    abq := hccw ia ib iq hab (by omega) hq
    acq := hccw ia ic iq (by omega) hcq hq
    bcq := hccw ib ic iq hbc hcq hq
  }

/-- First actual A3 pruning pattern of the C++ verifier:
row at B includes P,A, and row at C includes Q,A,B.
The third C spoke gives CA=CB, rather than an unexplained inequality. -/
theorem fiveCCW_forbids_pattern_BC
    (p a b c q : XY) (h : FiveCCW p a b c q)
    (hBPBA : sqDist b p = sqDist b a)
    (hCQCA : sqDist c q = sqDist c a)
    (hCACB : sqDist c a = sqDist c b) : False := by
  exact five_point_euclidean_impossible p a b c q
    h.pab h.abc h.abq h.paq h.acq h.bcq
    hBPBA hCQCA (le_of_eq hCACB)

/-- Reflected second actual A3 pruning pattern:
row at A includes P,B,C; row at B includes Q,C.
After reversal Q,C,B,A,P and reflection, it is the same five-point lemma. -/
theorem fiveCCW_forbids_pattern_AB
    (p a b c q : XY) (h : FiveCCW p a b c q)
    (hAPAC : sqDist a p = sqDist a c)
    (hACAB : sqDist a c = sqDist a b)
    (hBQBC : sqDist b q = sqDist b c) : False := by
  have hh1 := reflectY_reverse_positive q c b h.bcq
  have hh2 := reflectY_reverse_positive c b a h.abc
  have hh3 := reflectY_reverse_positive c b p h.pbc
  have hh4 := reflectY_reverse_positive q c p h.pcq
  have hh5 := reflectY_reverse_positive c a p h.pac
  have hh6 := reflectY_reverse_positive b a p h.pab
  have hB : sqDist (reflectY b) (reflectY q) =
      sqDist (reflectY b) (reflectY c) := by
    simpa only [reflectY_sqDist] using hBQBC
  have hA : sqDist (reflectY a) (reflectY p) =
      sqDist (reflectY a) (reflectY c) := by
    simpa only [reflectY_sqDist] using hAPAC
  have hC : sqDist (reflectY a) (reflectY c) ≤
      sqDist (reflectY a) (reflectY b) := by
    simpa only [reflectY_sqDist] using (le_of_eq hACAB)
  exact five_point_euclidean_impossible
    (reflectY q) (reflectY c) (reflectY b)
    (reflectY a) (reflectY p)
    hh1 hh2 hh3 hh4 hh5 hh6 hB hA hC

#print axioms E97A3.FiveCCW.rotate
#print axioms E97A3.FiveCCW.five_rotations
#print axioms E97A3.FiveCCW.of_increasing
#print axioms E97A3.fiveCCW_forbids_pattern_BC
#print axioms E97A3.fiveCCW_forbids_pattern_AB
end E97A3
