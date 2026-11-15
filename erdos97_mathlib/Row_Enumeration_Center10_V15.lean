import Row_Enumeration_Defs_V15
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97RowEnumeration15
theorem center10_complete : enumeratedWitnessSets 10 = allFourWitnessSets 10 := by
  decide +kernel
#print axioms E97RowEnumeration15.center10_complete
end E97RowEnumeration15
