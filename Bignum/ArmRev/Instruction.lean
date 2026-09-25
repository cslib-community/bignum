/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Guilherme Lima
-/
module

public import Bignum.BitVec
public import Bignum.Component

@[expose] public section

set_option autoImplicit false

namespace Bignum.ArmRev

/--
Micro-architectural (uarch) events.
-/
inductive UArchEvent where
  | EventLoad (addr : BitVec 64) (byte_length : Nat)
  | EventStore (addr : BitVec 64) (byte_length : Nat)
  | EventJump (src_PC : BitVec 64) (dest_PC : BitVec 64)

/--
The ARM machine state.
-/
structure State where
  /-- Program counter. -/
  _PC : BitVec 64

  /-- 31 general purpose registers (0-30) plus SP (register 31). -/
  _registers : BitVec 5 → BitVec 64

  /-- 32 SIMD registers. -/
  _simdregisters : BitVec 5 → BitVec 128

  /-- NZCV flags. -/
  _flags : BitVec 4

  /-- Byte-addressable memory with a 64-bit address space. -/
  _memory : BitVec 64 → BitVec 8

  /-- Observable uarch events. -/
  _events : List UArchEvent

namespace State

/-- The all zeros state. -/
def allZeros : State := {
  _PC            := 0
  _registers     := λ _ ↦ 0
  _simdregisters := λ _ ↦ 0
  _flags         := 0
  _memory        := λ _ ↦ 0
  _events        := []
}

/-- The all ones state. -/
def allOnes : State := {
  _PC            := BitVec.allOnes 64
  _registers     := λ _ ↦ BitVec.allOnes 64
  _simdregisters := λ _ ↦ BitVec.allOnes 128
  _flags         := BitVec.allOnes 4
  _memory        := λ _ ↦ BitVec.allOnes 8,
  _events        := []
}

instance : Inhabited State where
  default := allZeros

def PC : Component State (BitVec 64) :=
  ⟨λ s ↦ s._PC, λ x s ↦ {s with _PC := x}⟩

def registers : Component State (BitVec 5 → BitVec 64) :=
  ⟨λ s ↦ s._registers, λ x s ↦ {s with _registers := x}⟩

def simdregisters : Component State (BitVec 5 → BitVec 128) :=
  ⟨λ s ↦ s._simdregisters, λ x s ↦ {s with _simdregisters := x}⟩

def flags : Component State (BitVec 4) :=
  ⟨λ s ↦ s._flags, λ x s ↦ {s with _flags := x}⟩

def memory : Component State (BitVec 64 → BitVec 8) :=
  ⟨λ s ↦ s._memory, λ x s ↦ {s with _memory := x}⟩

def events : Component State (List UArchEvent) :=
  ⟨λ s ↦ s._events, λ x s ↦ {s with _events := x}⟩

/-- The negative condition flag. -/
def NF : Component State Bool :=
  flags :> .bitelement 3

/-- The zero condition flag. -/
def ZF : Component State Bool :=
  flags :> .bitelement 2

/-- The carry condition flag. -/
def CF : Component State Bool :=
  flags :> .bitelement 1

/-- The overflow condition flag. -/
def VF : Component State Bool :=
  flags :> .bitelement 0

/-- The zero register: zero as source, ignored as destination. -/
def XZR : Component State (BitVec 64) :=
  .rvalue 0#64

/-- Bottom 32-bits of the zero register, ignored as destination. -/
def WZR : Component State (BitVec 32) :=
  XZR :> .bottom_32

/-- Generic version of XZR. -/
def ZR {w : Nat} : Component State (BitVec w) :=
  .rvalue 0

/-- Main integer registers. -/
def XREG (n : Nat) : Component State (BitVec 64) :=
  if n ≥ 31 then XZR else registers :> .element n

def X0   := XREG 0
def X1   := XREG 1
def X2   := XREG 2
def X3   := XREG 3
def X4   := XREG 4
def X5   := XREG 5
def X6   := XREG 6
def X7   := XREG 7
def X8   := XREG 8
def X9   := XREG 9
def X10  := XREG 10
def X11  := XREG 11
def X12  := XREG 12
def X13  := XREG 13
def X14  := XREG 14
def X15  := XREG 15
def X16  := XREG 16
def X17  := XREG 17
def X18  := XREG 18
def X19  := XREG 19
def X20  := XREG 20
def X21  := XREG 21
def X22  := XREG 22
def X23  := XREG 23
def X24  := XREG 24
def X25  := XREG 25
def X26  := XREG 26
def X27  := XREG 27
def X28  := XREG 28
def X29  := XREG 29
def X30  := XREG 30

/-- Stack pointer. -/
def SP := registers :> .element 31

/-- 32-bit versions of the main registers. -/
def WREG (n : Nat) : Component State (BitVec 32) :=
  XREG n :> .zerotop_32

def W0   := WREG 0
def W1   := WREG 1
def W2   := WREG 2
def W3   := WREG 3
def W4   := WREG 4
def W5   := WREG 5
def W6   := WREG 6
def W7   := WREG 7
def W8   := WREG 8
def W9   := WREG 9
def W10  := WREG 10
def W11  := WREG 11
def W12  := WREG 12
def W13  := WREG 13
def W14  := WREG 14
def W15  := WREG 15
def W16  := WREG 16
def W17  := WREG 17
def W18  := WREG 18
def W19  := WREG 19
def W20  := WREG 20
def W21  := WREG 21
def W22  := WREG 22
def W23  := WREG 23
def W24  := WREG 24
def W25  := WREG 25
def W26  := WREG 26
def W27  := WREG 27
def W28  := WREG 28
def W29  := WREG 29
def W30  := WREG 30
def WSP  := SP :> .zerotop_32

end State

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
deriving DecidableEq, Repr

instance : ToString ShiftType where
  toString a := toString (repr a)

namespace ShiftType

/--
Perform the shift operation indicated by `sty` on `bv`.
-/
@[simp]
def shift (sty : ShiftType) (sa : BitVec 6) {n : Nat} (bv : BitVec n) :
    BitVec n :=
  match sty with
  | .LSL => bv.shiftLeft sa.toNat
  | .LSR => bv.ushiftRight sa.toNat
  | .ASR => bv.sshiftRight sa.toNat
  | .ROR => bv.rotateRight sa.toNat

end ShiftType

/--
Shifted version of register `reg` (writes are no-ops).
-/
def State.shifted (sty : ShiftType) (sa : Nat) {n : Nat}
    (reg : Component State (BitVec n)) : Component State (BitVec n) :=
  ⟨λ s ↦ sty.shift sa (Component.read reg s), Component.write reg⟩

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

/--
Extended version of register `reg` (writes are undefined).
-/
def State.extended (xty : ExtendedType) {n m : Nat}
    (reg : Component State (BitVec n)) : Component State (BitVec m) :=
  -- We use of `default` on the right as a substitute for HOL Light's ARB.
  ⟨λ s ↦ xty.extend (Component.read reg s), default⟩

namespace State

/-- The main SIMD registers. -/
def QREG (n : Nat) : Component State (BitVec 128) :=
  simdregisters :> .element n

def DREG (n : Nat) : Component State (BitVec 64) :=
  QREG n :> .zerotop_64

def SREG (n : Nat) : Component State (BitVec 32) :=
  DREG n :> .zerotop_32

def HREG (n : Nat) : Component State (BitVec 16) :=
  SREG n :> .zerotop_16

def BREG (n : Nat) : Component State (BitVec 8) :=
  HREG n :> .zerotop_8

def Q0  := QREG 0
def Q1  := QREG 1
def Q2  := QREG 2
def Q3  := QREG 3
def Q4  := QREG 4
def Q5  := QREG 5
def Q6  := QREG 6
def Q7  := QREG 7
def Q8  := QREG 8
def Q9  := QREG 9
def Q10 := QREG 10
def Q11 := QREG 11
def Q12 := QREG 12
def Q13 := QREG 13
def Q14 := QREG 14
def Q15 := QREG 15
def Q16 := QREG 16
def Q17 := QREG 17
def Q18 := QREG 18
def Q19 := QREG 19
def Q20 := QREG 20
def Q21 := QREG 21
def Q22 := QREG 22
def Q23 := QREG 23
def Q24 := QREG 24
def Q25 := QREG 25
def Q26 := QREG 26
def Q27 := QREG 27
def Q28 := QREG 28
def Q29 := QREG 29
def Q30 := QREG 30
def Q31 := QREG 31

def D0  := DREG 0
def D1  := DREG 1
def D2  := DREG 2
def D3  := DREG 3
def D4  := DREG 4
def D5  := DREG 5
def D6  := DREG 6
def D7  := DREG 7
def D8  := DREG 8
def D9  := DREG 9
def D10 := DREG 10
def D11 := DREG 11
def D12 := DREG 12
def D13 := DREG 13
def D14 := DREG 14
def D15 := DREG 15
def D16 := DREG 16
def D17 := DREG 17
def D18 := DREG 18
def D19 := DREG 19
def D20 := DREG 20
def D21 := DREG 21
def D22 := DREG 22
def D23 := DREG 23
def D24 := DREG 24
def D25 := DREG 25
def D26 := DREG 26
def D27 := DREG 27
def D28 := DREG 28
def D29 := DREG 29
def D30 := DREG 30
def D31 := DREG 31

/--
SIMD register lanes (writes are no-ops).
-/
def LANE_B (i : Nat) : Component (BitVec 128) (BitVec 128) :=
  .through (λ bv ↦ .replicate 16 (bv.extractLsb' (8 * i) 8)) id

def LANE_H (i : Nat) : Component (BitVec 128) (BitVec 128) :=
  .through (λ bv ↦ .replicate 8 (bv.extractLsb' (16 * i) 16)) id

def LANE_S (i : Nat) : Component (BitVec 128) (BitVec 128) :=
  .through (λ bv ↦ .replicate 4 (bv.extractLsb' (32 * i) 32)) id

def LANE_D (i : Nat) : Component (BitVec 128) (BitVec 128) :=
  .through (λ bv ↦ .replicate 2 (bv.extractLsb' (64 * i) 64)) id

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

theorem invert_condition (c : Condition) :
    c.invert = Condition.ofBitVec (c.toBitVec.xor 1) := by
  cases c <;> simp [ofBitVec, toBitVec, invert]

theorem invert_condition_involutive (c : Condition) :
    c.invert.invert = c := by
  cases c <;> simp [invert_condition, ofBitVec, toBitVec]

end Condition

/--
Tests whether the given condition holds in state `s`.
-/
def condition (s : State) : Condition → Bool
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

end State
end Bignum.ArmRev
