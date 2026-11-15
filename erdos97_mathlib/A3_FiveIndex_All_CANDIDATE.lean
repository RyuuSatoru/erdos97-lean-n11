import A3_FiveIndex_Block_00_CANDIDATE
import A3_FiveIndex_Block_01_CANDIDATE
import A3_FiveIndex_Block_02_CANDIDATE
import A3_FiveIndex_Block_03_CANDIDATE
import A3_FiveIndex_Block_04_CANDIDATE
import A3_FiveIndex_Block_05_CANDIDATE
import A3_FiveIndex_Block_06_CANDIDATE
import A3_FiveIndex_Block_07_CANDIDATE
import A3_FiveIndex_Block_08_CANDIDATE
import A3_FiveIndex_Block_09_CANDIDATE
import A3_FiveIndex_Block_10_CANDIDATE
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97A3Index
/-- All 462 5-subsets have five strictly increasing indices below 11. -/
theorem five_valid_of_lt (i : Nat) (hi : i < 462) :
    fiveIndex i 0 < fiveIndex i 1 ∧
    fiveIndex i 1 < fiveIndex i 2 ∧
    fiveIndex i 2 < fiveIndex i 3 ∧
    fiveIndex i 3 < fiveIndex i 4 ∧
    fiveIndex i 4 < 11 := by
  have from_chunk (start : Nat) (hstart : start ≤ i) (hend : i < start + 42)
      (hchunk : (List.range 42).all
        (fun j => validFiveIndex (start + j)) = true) :
      validFiveIndex i = true := by
    have hj : i - start < 42 := by omega
    have h := (List.all_eq_true.mp hchunk) (i - start) (List.mem_range.mpr hj)
    have heq : start + (i - start) = i := by omega
    simpa [heq] using h
  have hb : validFiveIndex i = true := by
    by_cases h0 : i < 42
    · exact from_chunk 0 (by omega) (by omega) E97A3IndexBlock00.chunk_ok
    by_cases h1 : i < 84
    · exact from_chunk 42 (by omega) (by omega) E97A3IndexBlock01.chunk_ok
    by_cases h2 : i < 126
    · exact from_chunk 84 (by omega) (by omega) E97A3IndexBlock02.chunk_ok
    by_cases h3 : i < 168
    · exact from_chunk 126 (by omega) (by omega) E97A3IndexBlock03.chunk_ok
    by_cases h4 : i < 210
    · exact from_chunk 168 (by omega) (by omega) E97A3IndexBlock04.chunk_ok
    by_cases h5 : i < 252
    · exact from_chunk 210 (by omega) (by omega) E97A3IndexBlock05.chunk_ok
    by_cases h6 : i < 294
    · exact from_chunk 252 (by omega) (by omega) E97A3IndexBlock06.chunk_ok
    by_cases h7 : i < 336
    · exact from_chunk 294 (by omega) (by omega) E97A3IndexBlock07.chunk_ok
    by_cases h8 : i < 378
    · exact from_chunk 336 (by omega) (by omega) E97A3IndexBlock08.chunk_ok
    by_cases h9 : i < 420
    · exact from_chunk 378 (by omega) (by omega) E97A3IndexBlock09.chunk_ok
    exact from_chunk 420 (by omega) (by omega) E97A3IndexBlock10.chunk_ok
  simpa [validFiveIndex] using hb

#print axioms E97A3Index.five_valid_of_lt
end E97A3Index
