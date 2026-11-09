/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Bignum.Arm.Decode
public import Bignum.Arm.State
public import Bignum.BitVec

@[expose] public section

/-! # Simplified model of ARM semantics -/

namespace Bignum.Arm

/--
Fetches and decodes the 4-byte, little-endian instruction at aligned `addr`.
-/
def State.decode (s : State) (addr : BitVec 64) : Option (Rel State State) :=
  if 4 ∣ addr.toNat then
    Decode.decode ((s.read memory).readBytesLE addr 4).toBitVecLE
  else
    none

-- theorem State.decode_cons
--     (s : State) (addr : BitVec 64) (bs bs' : ByteList)
--     (data : BitVec 32) (instr : Rel State State) :
--     s.AlignedBytesLoaded addr bs →
--     (bs.popBitVecLE 4) = .some (data, bs') →
--     Decode.decode data = .some instr →
--     s.decode addr = .some instr ∧ s.AlignedBytesLoaded (addr + 4) bs' := by
--   intro hA hpop hD;
--   constructor
--   · sorry
--   · rcases (bs.popBitVecLE_eq_some_iff _ _ _).mp hpop with ⟨hn, hl, hr⟩
--     sorry

/--
The fetch-decode-execute relation asserting that fetching, decoding, and
executing the current instruction in state `s` leads to state `s'`.
-/
def arm : Rel State State := fun s s' ↦
  match s.decode (s.read PC) with
  | .none => False
  | .some instr => (PC ≔ (s.read PC + 4#64) ,, instr) s s'

end Bignum.Arm
