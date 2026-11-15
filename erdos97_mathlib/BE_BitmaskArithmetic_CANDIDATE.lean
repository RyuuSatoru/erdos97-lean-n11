import Mathlib

/-!
Erdos #97: exact Nat bitwise-mask semantics on eleven vertex bits.
This is an independent, finite, kernel-checkable bridge.  No tree input
and no assumption about geometry.  Range 0..2047 covers every 11-bit mask.
The pair/triple indices are increasing; permutations and connection to the
A3 orientation patterns are a separate formal step.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace E97Bitmask

/-- Bit representing vertex `u`. -/
def bit (u : Nat) : Nat := 2 ^ u

def containsMask (m pattern : Nat) : Bool := decide ((m &&& pattern) = pattern)
def hasBit (m u : Nat) : Bool := containsMask m (bit u)
def twoBits (u v : Nat) : Nat := bit u ||| bit v
def threeBits (u v w : Nat) : Nat := (bit u ||| bit v) ||| bit w

/-- The real C++ test `(row.mask & requested_mask) == requested_mask`
for two increasing distinct requested vertices. -/
def pairCheck (m u v : Nat) : Bool :=
  containsMask m (twoBits u v) == (hasBit m u && hasBit m v)

/-- The same C++ mask-inclusion test for three increasing vertices. -/
def tripleCheck (m u v w : Nat) : Bool :=
  containsMask m (threeBits u v w) ==
    (hasBit m u && hasBit m v && hasBit m w)

/-- No geometric assumptions: finite verification of all 2048 11-bit
masks and the 55 increasing vertex pairs. -/
def allPairsCorrect : Bool :=
  (List.range 2048).all (fun m =>
    (List.range 11).all (fun u =>
      (List.range 11).all (fun v =>
        if u < v then pairCheck m u v else true)))

/-- Finite verification of all 2048 masks and 165 increasing triples. -/
def allTriplesCorrect : Bool :=
  (List.range 2048).all (fun m =>
    (List.range 11).all (fun u =>
      (List.range 11).all (fun v =>
        if u < v then
          (List.range 11).all (fun w =>
            if v < w then tripleCheck m u v w else true)
        else true)))

theorem allPairsCorrect_true : allPairsCorrect = true := by decide
theorem allTriplesCorrect_true : allTriplesCorrect = true := by decide

/-- General extraction from the kernel-checked finite pair scan. -/
theorem pair_inclusion_exact (m u v : Nat)
    (hm : m < 2048) (hu : u < 11) (hv : v < 11) (huv : u < v) :
    containsMask m (twoBits u v) = (hasBit m u && hasBit m v) := by
  have h0 := (List.all_eq_true.mp allPairsCorrect_true) m (List.mem_range.mpr hm)
  have h1 := (List.all_eq_true.mp h0) u (List.mem_range.mpr hu)
  have h2 := (List.all_eq_true.mp h1) v (List.mem_range.mpr hv)
  simpa [huv, pairCheck] using h2

/-- General extraction from the kernel-checked finite triple scan. -/
theorem triple_inclusion_exact (m u v w : Nat)
    (hm : m < 2048) (hu : u < 11) (hv : v < 11) (hw : w < 11)
    (huv : u < v) (hvw : v < w) :
    containsMask m (threeBits u v w) =
      (hasBit m u && hasBit m v && hasBit m w) := by
  have h0 := (List.all_eq_true.mp allTriplesCorrect_true) m (List.mem_range.mpr hm)
  have h1 := (List.all_eq_true.mp h0) u (List.mem_range.mpr hu)
  have h2 := (List.all_eq_true.mp h1) v (List.mem_range.mpr hv)
  -- Eliminate the first conditional before invoking List.all_eq_true.
  -- Keeping the inner List.all as a Bool avoids over-simplifying it into ∀.
  split_ifs at h2
  have h3 := (List.all_eq_true.mp h2) w (List.mem_range.mpr hw)
  simpa [hvw, tripleCheck] using h3

#print axioms E97Bitmask.allPairsCorrect_true
#print axioms E97Bitmask.allTriplesCorrect_true
#print axioms E97Bitmask.pair_inclusion_exact
#print axioms E97Bitmask.triple_inclusion_exact
end E97Bitmask
