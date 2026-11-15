import Certified_Mask_Data_V32
import Kernel_Reason_Data_V28
set_option autoImplicit false
namespace T32Table
def validSlot (slot : Nat) : Bool :=
  T32Mask.allowedAt slot ||
    (decide (T28Reason.reasonAt slot ≠ 0) &&
      T29E97FastTables19.fastCheckReason slot (T28Reason.reasonAt slot))
def validRow (pair row : Nat) : Bool :=
  (List.range 210).all (fun col => validSlot (44100*pair+210*row+col))
def Certified : Prop := ∀ slot, slot < 2425500 → T32Mask.allowedAt slot = false →
  T28Reason.reasonAt slot ≠ 0 ∧
    T29E97FastTables19.fastCheckReason slot (T28Reason.reasonAt slot) = true
end T32Table
