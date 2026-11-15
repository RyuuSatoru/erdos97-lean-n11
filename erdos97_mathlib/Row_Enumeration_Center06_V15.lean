import Row_Enumeration_Defs_V15
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97RowEnumeration15
theorem center06_complete : enumeratedWitnessSets 6 = allFourWitnessSets 6 := by
  decide +kernel
#print axioms E97RowEnumeration15.center06_complete
end E97RowEnumeration15
