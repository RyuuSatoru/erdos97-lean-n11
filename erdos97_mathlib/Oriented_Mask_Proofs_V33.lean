import Oriented_Mask_Core_V33
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
namespace T33Table
theorem all_cons {α : Type} {p : α → Bool} {x : α} {xs : List α}
    (hx : p x = true) (hxs : xs.all p = true) : (x :: xs).all p = true := by
  change (p x && xs.all p) = true
  rw [hx,hxs]
  rfl
theorem all_nil {α : Type} {p : α → Bool} : ([] : List α).all p = true := rfl
theorem certified_of_rows
    (hrows : ∀ a, a < 11 → ∀ b, b < 11 → ∀ x, x < 210 → validRow a b x = true) : Certified := by
  intro p hp c hc k hk ha
  have hb : p/210 < 11 := by omega
  have hx : p%210 < 210 := Nat.mod_lt _ (by omega)
  have h := (List.all_eq_true.mp (hrows (p/210) hb c hc (p%210) hx)) k (List.mem_range.mpr hk)
  have heq : 210*(p/210)+p%210 = p := by omega
  change validCell (p/210) c (p%210) k = true at h
  simpa only [validCell,heq,ha,Bool.false_or] using h
#print axioms T33Table.certified_of_rows
end T33Table
