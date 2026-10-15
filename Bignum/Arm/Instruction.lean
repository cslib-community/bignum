/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Bignum.Arm.Abbrev
public import Bignum.Arm.State

@[expose] public section

/-! # The ARM (aarch64) instructions -/

namespace Bignum.Arm

universe u

/--
Condition codes.
-/
inductive Condition where
  /-- Equal. -/
  | EQ
  /-- Not equal. -/
  | NE
  /-- Carry set. -/
  | CS
  /-- Carry clear. -/
  | CC
  /-- Minus, negative. -/
  | MI
  /-- Plus, positive or zero. -/
  | PL
  /-- Overflow. -/
  | VS
  /-- No overflow. -/
  | VC
  /-- Unsigned higher. -/
  | HI
  /-- Unsigned lower or same. -/
  | LS
  /-- Signed greater than or equal. -/
  | GE
  /-- Signed less than. -/
  | LT
  /-- Signed greater than. -/
  | GT
  /-- Signed less than or equal. -/
  | LE
  /-- Always. -/
  | AL
  /-- Always. -/
  | NV
deriving DecidableEq, Inhabited, Repr

namespace Condition

/-- Alias for CS (carry set). -/
abbrev HS := CS

/-- Alias for CC (carry clear). -/
abbrev LO := CC

/--
Converts condition code to 4-bit encoding.
-/
def toBitVec :  Condition → BitVec 4
  | EQ => 0b0000
  | NE => 0b0001
  | CS => 0b0010
  | CC => 0b0011
  | MI => 0b0100
  | PL => 0b0101
  | VS => 0b0110
  | VC => 0b0111
  | HI => 0b1000
  | LS => 0b1001
  | GE => 0b1010
  | LT => 0b1011
  | GT => 0b1100
  | LE => 0b1101
  | AL => 0b1110
  | NV => 0b1111

/--
Converts 4-bit encoding to condition code.
-/
def ofBitVec (bv : BitVec 4) : Condition :=
  match_bv bv with
  | [0000] => EQ
  | [0001] => NE
  | [0010] => CS
  | [0011] => CC
  | [0100] => MI
  | [0101] => PL
  | [0110] => VS
  | [0111] => VC
  | [1000] => HI
  | [1001] => LS
  | [1010] => GE
  | [1011] => LT
  | [1100] => GT
  | [1101] => LE
  | [1110] => AL
  | [1111] => NV
  | _ => panic! "should not get here"

/--
Inverts condition code.
-/
def invert : Condition → Condition
  | EQ => NE
  | NE => EQ
  | CS => CC
  | CC => CS
  | MI => PL
  | PL => MI
  | VS => VC
  | VC => VS
  | HI => LS
  | LS => HI
  | GE => LT
  | LT => GE
  | GT => LE
  | LE => GT
  | AL => NV
  | NV => AL

end Condition

/--
Tests whether the given condition holds in state `s`.
-/
def State.condition (s : State) : Condition → Bool
  | .EQ => ZF.read s
  | .NE => !ZF.read s
  | .CS => CF.read s
  | .CC => !CF.read s
  | .MI => NF.read s
  | .PL => !NF.read s
  | .VS => VF.read s
  | .VC => !VF.read s
  | .HI => CF.read s && !ZF.read s
  | .LS => !(CF.read s && !ZF.read s)
  | .GE => NF.read s == VF.read s
  | .LT => !(NF.read s == VF.read s)
  | .GT => !ZF.read s && (NF.read s == VF.read s)
  | .LE => !(!ZF.read s && (NF.read s == VF.read s))
  | .AL => true
  | .NV => true

/--
Addressing modes and offsets for loads and stores (LDP, LDR, STP, STR).
-/
inductive OffsetType where
  /-- [base, reg] -/
  | register (reg : Component State (BitVec 64))
  /-- [base, reg, LSL k] -/
  | shiftreg (reg : Component State (BitVec 64)) (k : Nat)
  /-- [base], [reg] -/
  | postreg (reg : Component State (BitVec 64))
  /-- [base, #n] or [base] -/
  | immediate (bv : BitVec 64)
  /-- [base, #n]! -/
  | preimmediate (bv : BitVec 64)
  /-- [base], #n -/
  | postimmediate (bv : BitVec 64)

namespace OffsetType

/-- Whether the offset type implies a writeback. -/
def writesback (oty : OffsetType) : Bool :=
  match oty with
  | .register _ => false
  | .shiftreg _ _ => false
  | .postreg _ => true
  | .immediate _ => false
  | .preimmediate _ => true
  | .postimmediate _ => true

/-- Alias for no offset. -/
abbrev no_offset : OffsetType := .immediate 0

end OffsetType

/-- The actual address offset used (0 for post-index). -/
def State.offset_address (s : State) (oty : OffsetType) : BitVec 64 :=
  match oty with
  | .register reg => reg.read s
  | .shiftreg reg k => (reg.read s).shiftLeft k
  | .postreg _ => 0
  | .immediate bv => bv
  | .preimmediate bv => bv
  | .postimmediate _ => 0

/-- The offset to add to the register. -/
def State.offset_writeback (s : State) (oty : OffsetType) : BitVec 64 :=
  match oty with
  | .register _ => 0
  | .shiftreg _ _ => 0
  | .postreg reg => reg.read s
  | .immediate _ => 0
  | .preimmediate bv => bv
  | .postimmediate bv => bv

/-! ## Memory components -/

/-- Multi-byte chunk of memory in little-endian encoding. -/
def bytes (addr : BitVec 64) (len : Nat) :
    Component State ByteList :=
  memory :> .bytesLE addr len

/-! ## General register-register instructions -/

def ADD {α : Type u} {w : Nat}
    (Rd : Component α (BitVec w))
    (Rm : Component α (BitVec w))
    (Rn : Component α (BitVec w))
    (s : α) : α → Prop :=
  let m := Rm.read s
  let n := Rn.read s
  let d : BitVec w := m + n
  (Rd ≔ d) s

def SUB {α : Type u} {w : Nat}
    (Rd : Component α (BitVec w))
    (Rm : Component α (BitVec w))
    (Rn : Component α (BitVec w))
    (s : α) : α → Prop :=
  let m := Rm.read s
  let n := Rn.read s
  let d : BitVec w := m - n
  (Rd ≔ d) s

end Bignum.Arm
