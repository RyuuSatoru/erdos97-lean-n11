import RowMask_Bridge_Core_CANDIDATE
import RowMask_Center_00_CANDIDATE
import RowMask_Center_01_CANDIDATE
import RowMask_Center_02_CANDIDATE
import RowMask_Center_03_CANDIDATE
import RowMask_Center_04_CANDIDATE
import RowMask_Center_05_CANDIDATE
import RowMask_Center_06_CANDIDATE
import RowMask_Center_07_CANDIDATE
import RowMask_Center_08_CANDIDATE
import RowMask_Center_09_CANDIDATE
import RowMask_Center_10_CANDIDATE

set_option autoImplicit false
set_option maxRecDepth 10000
namespace E97RowBridge
/-- General 2310-row theorem from eleven independently checked 210-row certificates. -/
theorem all_rows_agree (c k : Nat) (hc : c < 11) (hk : k < 210) :
    E97AllowFinite.rowMask c k = E97Bitmask.actualRowMask (210 * c + k) := by
  have hcases : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 ∨ c = 10 := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10
  · subst c
    have h : decide (E97AllowFinite.rowMask 0 k = E97Bitmask.actualRowMask (210 * 0 + k)) = true :=
      (List.all_eq_true.mp E97RowMaskC00.check) k (List.mem_range.mpr hk)
    exact decide_eq_true_eq.mp h
  · subst c
    have h : decide (E97AllowFinite.rowMask 1 k = E97Bitmask.actualRowMask (210 * 1 + k)) = true :=
      (List.all_eq_true.mp E97RowMaskC01.check) k (List.mem_range.mpr hk)
    exact decide_eq_true_eq.mp h
  · subst c
    have h : decide (E97AllowFinite.rowMask 2 k = E97Bitmask.actualRowMask (210 * 2 + k)) = true :=
      (List.all_eq_true.mp E97RowMaskC02.check) k (List.mem_range.mpr hk)
    exact decide_eq_true_eq.mp h
  · subst c
    have h : decide (E97AllowFinite.rowMask 3 k = E97Bitmask.actualRowMask (210 * 3 + k)) = true :=
      (List.all_eq_true.mp E97RowMaskC03.check) k (List.mem_range.mpr hk)
    exact decide_eq_true_eq.mp h
  · subst c
    have h : decide (E97AllowFinite.rowMask 4 k = E97Bitmask.actualRowMask (210 * 4 + k)) = true :=
      (List.all_eq_true.mp E97RowMaskC04.check) k (List.mem_range.mpr hk)
    exact decide_eq_true_eq.mp h
  · subst c
    have h : decide (E97AllowFinite.rowMask 5 k = E97Bitmask.actualRowMask (210 * 5 + k)) = true :=
      (List.all_eq_true.mp E97RowMaskC05.check) k (List.mem_range.mpr hk)
    exact decide_eq_true_eq.mp h
  · subst c
    have h : decide (E97AllowFinite.rowMask 6 k = E97Bitmask.actualRowMask (210 * 6 + k)) = true :=
      (List.all_eq_true.mp E97RowMaskC06.check) k (List.mem_range.mpr hk)
    exact decide_eq_true_eq.mp h
  · subst c
    have h : decide (E97AllowFinite.rowMask 7 k = E97Bitmask.actualRowMask (210 * 7 + k)) = true :=
      (List.all_eq_true.mp E97RowMaskC07.check) k (List.mem_range.mpr hk)
    exact decide_eq_true_eq.mp h
  · subst c
    have h : decide (E97AllowFinite.rowMask 8 k = E97Bitmask.actualRowMask (210 * 8 + k)) = true :=
      (List.all_eq_true.mp E97RowMaskC08.check) k (List.mem_range.mpr hk)
    exact decide_eq_true_eq.mp h
  · subst c
    have h : decide (E97AllowFinite.rowMask 9 k = E97Bitmask.actualRowMask (210 * 9 + k)) = true :=
      (List.all_eq_true.mp E97RowMaskC09.check) k (List.mem_range.mpr hk)
    exact decide_eq_true_eq.mp h
  · subst c
    have h : decide (E97AllowFinite.rowMask 10 k = E97Bitmask.actualRowMask (210 * 10 + k)) = true :=
      (List.all_eq_true.mp E97RowMaskC10.check) k (List.mem_range.mpr hk)
    exact decide_eq_true_eq.mp h
#print axioms E97RowBridge.all_rows_agree
end E97RowBridge
