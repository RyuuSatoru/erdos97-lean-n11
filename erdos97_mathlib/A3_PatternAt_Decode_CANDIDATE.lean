import A3_CyclicIndex_Geometry_CANDIDATE
import ReasonPayload_CANDIDATE
import BE_BitmaskArithmetic_CANDIDATE
/-!
A3 patternAt uses the very same five-subset and cyclic rotation as
E97A3Index.code_five_ccw. This is the missing *index/bitmask identity*,
not yet the entire checkReason_sound result.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
-- Proof tactic sequence avoids a redundant <;> focus operator.
-- `-DwarningAsError=true` and explicit #print axioms audits remain enabled.
set_option linter.unnecessarySeqFocus false
namespace E97A3Pattern
open E97AllowFinite E97A3Index E97Bitmask

/-- Independent readable reconstruction from the previously proved cyclic
five-index decoder. The BC and AB masks match the C++ pattern convention. -/
def decodedAt (id : Nat) : A3Pattern :=
  let i := id / 10
  let t := (id % 10) / 2
  let p := rot5 i t 0
  let a := rot5 i t 1
  let b := rot5 i t 2
  let c := rot5 i t 3
  let q := rot5 i t 4
  if id % 2 = 0 then
    ⟨b, c, twoBits p a, threeBits q a b⟩
  else
    ⟨a, b, threeBits p b c, twoBits q c⟩

/-- Uniform definitional connection between the finite checker and the
cyclic-five geometry decoder, for *every* Nat id (not only 0..4619). -/
theorem patternAt_eq_decodedAt (id : Nat) :
    patternAt id = decodedAt id := by
  have ht : (id % 10) / 2 < 5 := by omega
  -- After unfolding, the left side still contains an `Id.run` over
  -- the same if-branches as the right side.  Split on the parity branch;
  -- each branch is definitionally equal (the `Id` monad is the identity).
  simp [patternAt, decodedAt, rot5, fiveIndex,
        twoBits, threeBits, bit, Nat.mod_eq_of_lt ht]
  split_ifs <;> rfl

/-- A3 BC (even id) is exactly the bitmask payload expected by geometry. -/
theorem patternAt_bc (id : Nat) (heven : id % 2 = 0) :
    patternAt id =
      ⟨rot5 (id / 10) ((id % 10) / 2) 2,
       rot5 (id / 10) ((id % 10) / 2) 3,
       twoBits (rot5 (id / 10) ((id % 10) / 2) 0)
               (rot5 (id / 10) ((id % 10) / 2) 1),
       threeBits (rot5 (id / 10) ((id % 10) / 2) 4)
                 (rot5 (id / 10) ((id % 10) / 2) 1)
                 (rot5 (id / 10) ((id % 10) / 2) 2)⟩ := by
  rw [patternAt_eq_decodedAt]
  simp [decodedAt, heven]

/-- A3 AB (odd id) is exactly the reflected bitmask payload. -/
theorem patternAt_ab (id : Nat) (hodd : id % 2 ≠ 0) :
    patternAt id =
      ⟨rot5 (id / 10) ((id % 10) / 2) 1,
       rot5 (id / 10) ((id % 10) / 2) 2,
       threeBits (rot5 (id / 10) ((id % 10) / 2) 0)
                 (rot5 (id / 10) ((id % 10) / 2) 2)
                 (rot5 (id / 10) ((id % 10) / 2) 3),
       twoBits (rot5 (id / 10) ((id % 10) / 2) 4)
               (rot5 (id / 10) ((id % 10) / 2) 3)⟩ := by
  rw [patternAt_eq_decodedAt]
  simp [decodedAt, hodd]

#print axioms E97A3Pattern.patternAt_eq_decodedAt
#print axioms E97A3Pattern.patternAt_bc
#print axioms E97A3Pattern.patternAt_ab
end E97A3Pattern
