import Oriented_Mask_Data_V33
set_option autoImplicit false
namespace T33Table
def validCell (a b x y : Nat) : Bool :=
  (T33Data.rowMask (210*a+x) b).testBit y ||
    T32Checker.checkedPair [210*a+x] (210*b+y)
      ⟨T29E97HintSearch16.slotOfRows (210*a+x) (210*b+y),0⟩
def validRow (a b x : Nat) : Bool :=
  (List.range 210).all (fun y => validCell a b x y)
def Certified : Prop := ∀ p, p < 2310 → ∀ c, c < 11 → ∀ k, k < 210 →
  (T33Data.rowMask p c).testBit k = false →
    T32Checker.checkedPair [p] (210*c+k) ⟨T29E97HintSearch16.slotOfRows p (210*c+k),0⟩ = true
end T33Table
