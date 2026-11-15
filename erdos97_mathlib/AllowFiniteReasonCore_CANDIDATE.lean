import Mathlib
/-!
A kernel-reducible model for the *actual* combinatorial order of the E97
11-vertex allow-table certificate, without trusting precomputed masks.

This module does NOT establish geometric soundness of rejection reasons.
That is a separate theorem, already conditional on A1/A3 in other modules.
Nor does it prove the 2,425,500 cells until every shard compiles.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97AllowFinite

/-- Include-first combinations, exactly in C++ lexicographic order. -/
def chooseK (k : Nat) (vs : List Nat) : List (List Nat) :=
  match k, vs with
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, x :: xs =>
      (chooseK k xs).map (fun ys => x :: ys) ++ chooseK (k + 1) xs
termination_by structural vs

/-- The 55 lexicographically ordered center/vertex pairs. -/
def pairAt (id : Nat) : Nat × Nat :=
  let pair := (chooseK 2 (List.range 11)).getD id []
  (pair.getD 0 11, pair.getD 1 11)

/-- Four witnesses per center, in the original verifier's local order. -/
def witnessFour (center rowIx : Nat) : List Nat :=
  ((chooseK 4 ((List.range 11).filter (fun v => v != center))).getD rowIx [])

def rowMask (center rowIx : Nat) : Nat :=
  (witnessFour center rowIx).foldl (fun acc v => acc ||| (2 ^ v)) 0

/-- A3 patterns enumerate 462 sorted five-subsets, five rotations and
    BC followed by AB, giving 4620 reason IDs. -/
structure A3Pattern where
  c : Nat
  d : Nat
  mc : Nat
  md : Nat
  deriving Repr, DecidableEq

def patternAt (id : Nat) : A3Pattern := Id.run do
  let five := (chooseK 5 (List.range 11)).getD (id / 10) []
  let t := (id % 10) / 2
  let p := five.getD t 11
  let a := five.getD ((t + 1) % 5) 11
  let b := five.getD ((t + 2) % 5) 11
  let c := five.getD ((t + 3) % 5) 11
  let q := five.getD ((t + 4) % 5) 11
  if id % 2 = 0 then
    return ⟨b, c, (2 ^ p) ||| (2 ^ a), (2 ^ q) ||| (2 ^ a) ||| (2 ^ b)⟩
  else
    return ⟨a, b, (2 ^ p) ||| (2 ^ b) ||| (2 ^ c), (2 ^ q) ||| (2 ^ c)⟩

def containsBits (mask required : Nat) : Bool :=
  decide ((mask &&& required) = required)

def alternate (a b u v : Nat) : Bool :=
  decide ((a < u ∧ u < b) ≠ (a < v ∧ v < b))

/-- Decode exactly the row-major index:
   55 center-pairs × 210 rows at a × 210 rows at b. -/
def cellData (slot : Nat) : Nat × Nat × Nat × Nat × Nat × Nat :=
  let i := slot / 44100
  let j := slot % 44100
  let (a, b) := pairAt i
  let x := j / 210
  let y := j % 210
  (a, b, x, y, rowMask a x, rowMask b y)

/-- True means this cell either is allowed (code 0), or supplies a
    correct explicit A1/A3 rejection *witness* according to the integer
    operations of the original C++ verifier.

    The verifier does not assert that every allowed cell is geometrically
    realizable, which is unnecessary for a conservative domain filter. -/
def checkReason (slot code : Nat) : Bool :=
  if slot < 2425500 then
    if code = 0 then true
    else
      let (a, b, _x, _y, ma, mb) := cellData slot
      if code ≤ 55 then
        let (u, v) := pairAt (code - 1)
        containsBits ma ((2 ^ u) ||| (2 ^ v)) &&
        containsBits mb ((2 ^ u) ||| (2 ^ v)) &&
        (alternate a b u v == false)
      else if code ≤ 4675 then
        let pat := patternAt (code - 56)
        if pat.c = a ∧ pat.d = b then
          containsBits ma pat.mc && containsBits mb pat.md
        else if pat.c = b ∧ pat.d = a then
          containsBits mb pat.mc && containsBits ma pat.md
        else false
      else false
  else false

end E97AllowFinite
