import Row_Enumeration_Defs_V15
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97RowEnumeration15
theorem center04_complete : enumeratedWitnessSets 4 = allFourWitnessSets 4 := by
  decide +kernel
#print axioms E97RowEnumeration15.center04_complete
end E97RowEnumeration15
