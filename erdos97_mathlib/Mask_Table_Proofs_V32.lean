import Mask_Table_Core_V32
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
namespace T32Table
theorem all_cons {α : Type} {p : α → Bool} {x : α} {xs : List α}
    (hx : p x = true) (hxs : xs.all p = true) : (x :: xs).all p = true := by
  change (p x && xs.all p) = true
  rw [hx,hxs]
  rfl
theorem all_nil {α : Type} {p : α → Bool} : ([] : List α).all p = true := rfl
theorem certified_of_rows
    (hrows : ∀ pair, pair < 55 → ∀ row, row < 210 → validRow pair row = true) : Certified := by
  intro slot hs ha
  let pair := slot / 44100
  let row := slot % 44100 / 210
  let col := slot % 44100 % 210
  have hp : pair < 55 := by dsimp [pair]; omega
  have hr : row < 210 := by dsimp [row]; omega
  have hc : col < 210 := Nat.mod_lt _ (by omega)
  have hrow := hrows pair hp row hr
  have h := (List.all_eq_true.mp hrow) col (List.mem_range.mpr hc)
  have hindex : 44100*pair + 210*row + col = slot := by
    have h1 := Nat.mod_add_div slot 44100
    have h2 := Nat.mod_add_div (slot%44100) 210
    dsimp [pair,row,col]
    omega
  change validSlot (44100*pair + 210*row + col) = true at h
  rw [hindex] at h
  simpa only [validSlot,ha,Bool.false_or,Bool.and_eq_true,decide_eq_true_eq] using h
#print axioms T32Table.certified_of_rows
end T32Table
