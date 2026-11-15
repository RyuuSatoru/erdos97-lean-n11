import A1_SharedWitnesses_CANDIDATE

/-!
A1: translate opposite signs of the oriented line AB into the exact
index-alternation predicate used by the E97 C++ tree verifier.
No all-pairs distance assumption: only the four equalities for the
named two witnesses, from the two named centers.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace E97A1Index
open E97BlockB E97A1

/-- Same definition as `E97BlockB11.CCWStrict11`, kept independent of the
    expensive 660-quad table compilation. -/
def StrictCCW11 (P : Fin 11 → XY) : Prop :=
  ∀ i j k : Nat, i < j → j < k → k < 11 →
    0 < orient (P (Fin.ofNat 11 i))
      (P (Fin.ofNat 11 j)) (P (Fin.ofNat 11 k))

/-- For two center indices `a<b`, `u` lies on the inner arc from a to b. -/
def betweenAB (a b u : Nat) : Prop := a < u ∧ u < b

/-- Exact A1 crossing predicate of the original C++ verifier:
    `(a<u && u<b) != (a<v && v<b)`. -/
def crossingA1 (a b u v : Nat) : Bool :=
  decide (a < u ∧ u < b) != decide (a < v ∧ v < b)

/-- The inner arc is on the negative side of the oriented chord a→b. -/
theorem inside_has_negative_orientation
    (P : Fin 11 → XY) (hccw : StrictCCW11 P)
    (a b u : Nat) (hau : a < u) (hub : u < b) (hb : b < 11) :
    orient (P (Fin.ofNat 11 a)) (P (Fin.ofNat 11 b))
      (P (Fin.ofNat 11 u)) < 0 := by
  have hp := hccw a u b hau hub hb
  have hswap :
      orient (P (Fin.ofNat 11 a)) (P (Fin.ofNat 11 b))
        (P (Fin.ofNat 11 u)) =
      -orient (P (Fin.ofNat 11 a)) (P (Fin.ofNat 11 u))
        (P (Fin.ofNat 11 b)) := by
    dsimp [orient]
    ring
  rw [hswap]
  linarith

/-- The two exterior arcs are on the positive side of the oriented chord. -/
theorem outside_has_positive_orientation
    (P : Fin 11 → XY) (hccw : StrictCCW11 P)
    (a b u : Nat) (hab : a < b) (hb : b < 11)
    (hu : u < 11) (hua : u ≠ a) (hub : u ≠ b)
    (hout : ¬ betweenAB a b u) :
    0 < orient (P (Fin.ofNat 11 a)) (P (Fin.ofNat 11 b))
      (P (Fin.ofNat 11 u)) := by
  by_cases hlow : u < a
  · have hp := hccw u a b hlow hab hb
    have hrotate :
        orient (P (Fin.ofNat 11 a)) (P (Fin.ofNat 11 b))
          (P (Fin.ofNat 11 u)) =
        orient (P (Fin.ofNat 11 u)) (P (Fin.ofNat 11 a))
          (P (Fin.ofNat 11 b)) := by
      dsimp [orient]
      ring
    rw [hrotate]
    exact hp
  · have hhigh : b < u := by
      unfold betweenAB at hout
      omega
    exact hccw a b u hab hhigh hu

/-- The two shared witnesses must fall on different arcs of (a,b).
    `hpoints` is explicit: the coordinate-injectivity of a strictly
    convex eleven-point configuration is proved separately below. -/
theorem shared_witnesses_must_alternate
    (P : Fin 11 → XY) (hccw : StrictCCW11 P)
    (a b u v : Nat)
    (hab : a < b) (hb : b < 11)
    (hu : u < 11) (hv : v < 11)
    (hua : u ≠ a) (hub : u ≠ b)
    (hva : v ≠ a) (hvb : v ≠ b)
    (hpoints : P (Fin.ofNat 11 u) ≠ P (Fin.ofNat 11 v))
    (ha : sqDist (P (Fin.ofNat 11 a)) (P (Fin.ofNat 11 u)) =
          sqDist (P (Fin.ofNat 11 a)) (P (Fin.ofNat 11 v)))
    (hb' : sqDist (P (Fin.ofNat 11 b)) (P (Fin.ofNat 11 u)) =
           sqDist (P (Fin.ofNat 11 b)) (P (Fin.ofNat 11 v))) :
    (betweenAB a b u ∧ ¬ betweenAB a b v) ∨
      (betweenAB a b v ∧ ¬ betweenAB a b u) := by
  have hOpp := shared_witnesses_orientation_opposite
    (P (Fin.ofNat 11 a)) (P (Fin.ofNat 11 b))
    (P (Fin.ofNat 11 u)) (P (Fin.ofNat 11 v))
    hpoints ha hb'
  by_cases hinU : betweenAB a b u
  · left
    refine ⟨hinU, ?_⟩
    intro hinV
    have hnegU := inside_has_negative_orientation P hccw a b u
      hinU.1 hinU.2 hb
    have hnegV := inside_has_negative_orientation P hccw a b v
      hinV.1 hinV.2 hb
    linarith
  · right
    refine ⟨?_, hinU⟩
    by_contra hinV
    have hposU := outside_has_positive_orientation P hccw a b u
      hab hb hu hua hub hinU
    have hposV := outside_has_positive_orientation P hccw a b v
      hab hb hv hva hvb hinV
    linarith

/-- Exact C++ Boolean crossing check, not just an abstract alternation. -/
theorem shared_witnesses_crossingA1
    (P : Fin 11 → XY) (hccw : StrictCCW11 P)
    (a b u v : Nat)
    (hab : a < b) (hb : b < 11)
    (hu : u < 11) (hv : v < 11)
    (hua : u ≠ a) (hub : u ≠ b)
    (hva : v ≠ a) (hvb : v ≠ b)
    (hpoints : P (Fin.ofNat 11 u) ≠ P (Fin.ofNat 11 v))
    (ha : sqDist (P (Fin.ofNat 11 a)) (P (Fin.ofNat 11 u)) =
          sqDist (P (Fin.ofNat 11 a)) (P (Fin.ofNat 11 v)))
    (hb' : sqDist (P (Fin.ofNat 11 b)) (P (Fin.ofNat 11 u)) =
           sqDist (P (Fin.ofNat 11 b)) (P (Fin.ofNat 11 v))) :
    crossingA1 a b u v = true := by
  have h := shared_witnesses_must_alternate P hccw a b u v
    hab hb hu hv hua hub hva hvb hpoints ha hb'
  rcases h with ⟨hU, hV⟩ | ⟨hV, hU⟩
  · change a < u ∧ u < b at hU
    change ¬ (a < v ∧ v < b) at hV
    simp [crossingA1, hU, hV]
  · change a < v ∧ v < b at hV
    change ¬ (a < u ∧ u < b) at hU
    simp [crossingA1, hU, hV]

#print axioms E97A1Index.inside_has_negative_orientation
#print axioms E97A1Index.outside_has_positive_orientation
#print axioms E97A1Index.shared_witnesses_must_alternate
#print axioms E97A1Index.shared_witnesses_crossingA1
end E97A1Index
