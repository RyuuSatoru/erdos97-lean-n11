import Row_Enumeration_Defs_V15
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97RowEnumeration15
theorem center03_complete : enumeratedWitnessSets 3 = allFourWitnessSets 3 := by
  decide +kernel
#print axioms E97RowEnumeration15.center03_complete
end E97RowEnumeration15
