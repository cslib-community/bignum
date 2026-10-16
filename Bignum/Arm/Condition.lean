/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Bignum.BitVec

@[expose] public section

/-! # Conditions -/

namespace Bignum.Arm

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

theorem invert_ofBitVec_toBitVec_xor (c : Condition) :
    c.invert = Condition.ofBitVec (c.toBitVec.xor 1) := by
  cases c <;> simp [ofBitVec, toBitVec, invert]

theorem invert_involutive (c : Condition) :
    c.invert.invert = c := by
  cases c <;> simp [invert]

end Condition
end Bignum.Arm
