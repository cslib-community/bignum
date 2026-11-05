/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

import Bignum.BitVec

@[expose] public section

/-! # Register operands -/

namespace Bignum.Arm

/--
Shifted register operands.
-/
inductive ShiftType where
  /-- Logical left shift. -/
  | LSL
  /-- Logical right shift. -/
  | LSR
  /-- Arithmetic right shift. -/
  | ASR
  /-- Rotate right. -/
  | ROR
deriving DecidableEq, Inhabited, Repr

instance : ToString ShiftType where
  toString a := toString (repr a)

namespace ShiftType

/--
Converts 2-bit bitvector to shift type.
-/
def ofBitVec (bv : BitVec 2) : ShiftType :=
  match_bv bv with
  | [00] => .LSL
  | [01] => .LSR
  | [10] => .ASR
  | [11] => .ROR
  | _ => panic! "should not get here"

/--
Converts shift type to 2-bit bitvector.
-/
def toBitVec : ShiftType → BitVec 2
  | .LSL => 0b00
  | .LSR => 0b01
  | .ASR => 0b10
  | .ROR => 0b11

theorem ofBitVec_toBitVec :
    ∀ bv, (ShiftType.ofBitVec bv).toBitVec = bv := by
  decide

/--
Perform the given shift operation on `bv` by amount `sa`.
-/
@[simp]
def shift (sa : BitVec 6) {n : Nat} (bv : BitVec n) : ShiftType → BitVec n
  | .LSL => bv.shiftLeft sa.toNat
  | .LSR => bv.ushiftRight sa.toNat
  | .ASR => bv.sshiftRight sa.toNat
  | .ROR => bv.rotateRight sa.toNat

end ShiftType

/--
Extended register operands.
-/
inductive ExtendedType where
  /-- Unsigned byte. -/
  | UXTB
  /-- Unsigned half word. -/
  | UXTH
  /-- Unsigned word. -/
  | UXTW
  /-- Unsigned double word. -/
  | UXTX
  /-- Signed byte. -/
  | SXTB
  /-- Signed half word. -/
  | SXTH
  /-- Signed word. -/
  | SXTW
  /-- Signed double word. -/
  | SXTX
deriving DecidableEq, Repr

namespace ExtendedType

/--
Perform the extension operation indicated by `xty` on `bv`.
-/
@[simp]
def extend (xty : ExtendedType) {n m : Nat} (bv : BitVec n) : BitVec m :=
  match xty with
  | .UXTB => (bv.truncate 8).zeroExtend m
  | .UXTH => (bv.truncate 16).zeroExtend m
  | .UXTW => (bv.truncate 32).zeroExtend m
  | .UXTX => (bv.truncate 64).zeroExtend m
  | .SXTB => (bv.truncate 8).signExtend m
  | .SXTH => (bv.truncate 16).signExtend m
  | .SXTW => (bv.truncate 32).signExtend m
  | .SXTX => (bv.truncate 64).signExtend m

end ExtendedType
end Bignum.Arm
