import Row_Enumeration_Defs_V15
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97RowEnumeration15
theorem center02_complete : enumeratedWitnessSets 2 = allFourWitnessSets 2 := by
  decide +kernel
#print axioms E97RowEnumeration15.center02_complete
end E97RowEnumeration15
