import E97_RowRealization_Core
set_option autoImplicit false
namespace E97RowEnumeration15
def enumeratedWitnessSets (center : Nat) : Finset (Finset Nat) :=
  ((List.range 210).map (fun k => E97A2Prefix.rowWitnessSet (210*center+k))).toFinset
def allFourWitnessSets (center : Nat) : Finset (Finset Nat) :=
  ((Finset.range 11).erase center).powersetCard 4
end E97RowEnumeration15
