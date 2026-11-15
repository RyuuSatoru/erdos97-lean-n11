import A2_SelectedPrefixCounts_CANDIDATE
import A1_PointDistinct_CANDIDATE
set_option autoImplicit false
namespace E97A3
def SelectedRowEq (P : Fin 11 → E97BlockB.XY) (center : Nat)
    (witnesses : Finset Nat) : Prop :=
  ∀ u v : Nat, u ∈ witnesses → v ∈ witnesses →
    E97BlockB.sqDist (P (Fin.ofNat 11 center)) (P (Fin.ofNat 11 u)) =
    E97BlockB.sqDist (P (Fin.ofNat 11 center)) (P (Fin.ofNat 11 v))
end E97A3
namespace E97AllowSound
def SelectedRowRealization (P : Fin 11 → E97BlockB.XY) (row : Nat) : Prop :=
  E97A3.SelectedRowEq P (row / 210) (E97A2Prefix.rowWitnessSet row)
end E97AllowSound
