import CheckReason_PairOrder_CANDIDATE
/-!
Decode the actual row-major 2,425,500-slot table indexing.
All arithmetic obligations are symbolic; this does not scan the U16 certificate.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97CellSlot
open E97AllowFinite E97CheckReason

def centerA (slot : Nat) : Nat := (pairAt (slot / 44100)).1
def centerB (slot : Nat) : Nat := (pairAt (slot / 44100)).2
def rowX (slot : Nat) : Nat := slot % 44100 / 210
def rowY (slot : Nat) : Nat := slot % 44100 % 210

/-- Exact cellData decoding without an externally supplied hcell. -/
theorem cellData_exact (slot : Nat) :
    cellData slot =
      (centerA slot, centerB slot, rowX slot, rowY slot,
       rowMask (centerA slot) (rowX slot),
       rowMask (centerB slot) (rowY slot)) := by
  rcases hpair : pairAt (slot / 44100) with ⟨a, b⟩
  simp [cellData, centerA, centerB, rowX, rowY, hpair]

/-- Each actual slot uses increasing distinct centers and two valid rows. -/
theorem slot_bounds (slot : Nat) (hs : slot < 2425500) :
    centerA slot < centerB slot ∧ centerB slot < 11 ∧
    rowX slot < 210 ∧ rowY slot < 210 := by
  have hi : slot / 44100 < 55 := by omega
  have hab := pair_indices_wellformed (slot / 44100) hi
  have hrem : slot % 44100 < 44100 := Nat.mod_lt _ (by omega)
  have hx : rowX slot < 210 := by
    unfold rowX
    omega
  have hy : rowY slot < 210 := by
    unfold rowY
    omega
  exact ⟨hab.1, hab.2, hx, hy⟩

/-- No center order may be reversed by the slot decoder itself. -/
theorem slot_centers_increasing (slot : Nat) (hs : slot < 2425500) :
    centerA slot < centerB slot := (slot_bounds slot hs).1

#print axioms E97CellSlot.cellData_exact
#print axioms E97CellSlot.slot_bounds
#print axioms E97CellSlot.slot_centers_increasing
end E97CellSlot
