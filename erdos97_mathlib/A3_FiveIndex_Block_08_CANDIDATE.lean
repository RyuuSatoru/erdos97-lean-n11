import A3_FiveIndex_Core_CANDIDATE
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97A3IndexBlock08
open E97A3Index
/-- 42 five-subsets in block 8; actual include-first chooseK data. -/
theorem chunk_ok :
    (List.range 42).all (fun j => validFiveIndex (336 + j)) = true := by decide
#print axioms E97A3IndexBlock08.chunk_ok
end E97A3IndexBlock08
