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
Asserts that the 32-bit data corresponding to instruction `instr` is
loaded 4-byte-aligned into state's `s` memory at address `addr`.
-/
structure State.decode (s : State) (addr : BitVec 64) : Type where
  /-- Instruction. -/
  instr : Relation State State
  /-- Encoded instruction. -/
  data : BitVec 32
  /-- `data` is 4-byte-aligned and loaded at address `addr`. -/
  loaded : s.AlignedBytesLoaded addr (.ofNatLE 4 data.toNat)
  /-- When decoded, `data` produces instruction `instr`. -/
  decode : Decode.decode data = .some instr

/-
The basic fetch-decode-execute cycle.
-/
def arm : Relation State State := fun s s' ↦
  ∃ d : s.decode (s.read PC), (PC ≔ (s.read PC + 4#64) ,, d.instr) s s'

end Bignum.Arm
