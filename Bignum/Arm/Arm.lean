/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Bignum.Arm.Decode
public import Bignum.Arm.State
public import Bignum.Arm.StateLemmas
public import Bignum.BitVec

@[expose] public section

/-! # ARM semantics -/

namespace Bignum.Arm

namespace State

/-- Reads the 4-byte little-endian word at address `addr` as a bitvector. -/
def fetch (s : State) (addr : BitVec 64) : BitVec 32 :=
  (s.read $ bytes addr 4).toBitVecLE.cast (by rw [length_read_bytes])

/--
Decodes the 4-byte instruction loaded on memory at address `addr`.
Ensures that the address is 4-byte aligned.  Returns the encoded bitvector
and the resulting instruction if successful.
-/
def decode (s : State) (addr : BitVec 64) :
    Option (BitVec 32 × Rel State State) :=
  if 4 ∣ addr.toNat then
    let data := s.fetch addr
    match Decode.decode data with
    | none => none
    | some instr => some (data, instr)
  else
    none

/--
Asserts that decoding the instruction at address `addr` results in `instr`.
-/
def Decode (s : State) (addr : BitVec 64) (instr : Rel State State) : Prop :=
  ∃ data, s.decode addr = some (data, instr)

end State

/--
The fetch-decode-execute relation asserting that fetching, decoding, and
executing the current instruction in state `s` leads to state `s'`.
-/
def arm : Rel State State := fun s s' ↦
  match s.decode (s.read PC) with
  | none => False
  | some (_, instr) => (PC ≔ (s.read PC + 4#64) ,, instr) s s'

end Bignum.Arm
