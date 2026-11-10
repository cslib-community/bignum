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

/-! # ARM semantics -/

namespace Bignum.Arm

/--
Attempts to decode 4-byte encoded instruction at 4-byte aligned `addr`.
-/
def State.decodeAligned (s : State) (addr : BitVec 64) :
    4 ∣ addr.toNat → Option (Rel State State) :=
  fun _ ↦ Decode.decode (s.read $ bytes addr 4).toBitVecLE

/--
Attempts to decode 4-byte encoded instruction at arbitrary `addr`.
-/
def State.decode (s : State) (addr : BitVec 64) : Option (Rel State State) :=
  if ha : 4 ∣ addr.toNat then
    s.decodeAligned addr ha
  else
    none

/--
The fetch-decode-execute relation asserting that fetching, decoding, and
executing the current instruction in state `s` leads to state `s'`.
-/
def arm : Rel State State := fun s s' ↦
  match s.decode (s.read PC) with
  | none => False
  | some instr => (PC ≔ (s.read PC + 4#64) ,, instr) s s'

end Bignum.Arm
