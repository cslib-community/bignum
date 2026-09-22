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
  flags :> Component.bitelement 3

/-- The zero condition flag. -/
def ZF : Component State Bool :=
  flags :> Component.bitelement 2

/-- The carry condition flag. -/
def CF : Component State Bool :=
  flags :> Component.bitelement 1

/-- The overflow condition flag. -/
def VF : Component State Bool :=
  flags :> Component.bitelement 0

/-- The zero register: zero as source, ignored as destination. -/
def XZR : Component State (BitVec 64) :=
  Component.rvalue 0#64

theorem XZR_zero : XZR = Component.rvalue 0 := by
  rfl

#exit

def WZR (s : State) : BitVec 32 :=
  s.XZR.truncate 32

/-- Generic version of XZR. -/
def ZR (_ : State) {n : Nat} : BitVec n :=
  0

theorem WZR_zero (s : State) : s.WZR = 0 := by
  rfl

theorem ZR_zero (s : State) {n : Nat} : s.ZR = 0#n := by
  rfl

/-- Main integer registers. -/
def XREG (s : State) (n : Nat) : BitVec 64 :=
  if n ≤ 30 then s.registers n else s.XZR

def X0  (s : State) : BitVec 64 := s.XREG 0
def X1  (s : State) : BitVec 64 := s.XREG 1
def X2  (s : State) : BitVec 64 := s.XREG 2
def X3  (s : State) : BitVec 64 := s.XREG 3
def X4  (s : State) : BitVec 64 := s.XREG 4
def X5  (s : State) : BitVec 64 := s.XREG 5
def X6  (s : State) : BitVec 64 := s.XREG 6
def X7  (s : State) : BitVec 64 := s.XREG 7
def X8  (s : State) : BitVec 64 := s.XREG 8
def X9  (s : State) : BitVec 64 := s.XREG 9
def X10 (s : State) : BitVec 64 := s.XREG 10
def X11 (s : State) : BitVec 64 := s.XREG 11
def X12 (s : State) : BitVec 64 := s.XREG 12
def X13 (s : State) : BitVec 64 := s.XREG 13
def X14 (s : State) : BitVec 64 := s.XREG 14
def X15 (s : State) : BitVec 64 := s.XREG 15
def X16 (s : State) : BitVec 64 := s.XREG 16
def X17 (s : State) : BitVec 64 := s.XREG 17
def X18 (s : State) : BitVec 64 := s.XREG 18
def X19 (s : State) : BitVec 64 := s.XREG 19
def X20 (s : State) : BitVec 64 := s.XREG 20
def X21 (s : State) : BitVec 64 := s.XREG 21
def X22 (s : State) : BitVec 64 := s.XREG 22
def X23 (s : State) : BitVec 64 := s.XREG 23
def X24 (s : State) : BitVec 64 := s.XREG 24
def X25 (s : State) : BitVec 64 := s.XREG 25
def X26 (s : State) : BitVec 64 := s.XREG 26
def X27 (s : State) : BitVec 64 := s.XREG 27
def X28 (s : State) : BitVec 64 := s.XREG 28
def X29 (s : State) : BitVec 64 := s.XREG 29
def X30 (s : State) : BitVec 64 := s.XREG 30

theorem XREG31_zero (s : State) : s.XREG 31 = 0 := by
  rfl

/-- Stack pointer. --/
def SP (s : State) : BitVec 64 :=
  s.registers 31

/-- 32-bit versions of the main registers. -/
def WREG (s : State) (n : Nat) : BitVec 32 :=
  (s.XREG n).truncate 32

def W0  (s : State) : BitVec 32 := s.WREG 0
def W1  (s : State) : BitVec 32 := s.WREG 1
def W2  (s : State) : BitVec 32 := s.WREG 2
def W3  (s : State) : BitVec 32 := s.WREG 3
def W4  (s : State) : BitVec 32 := s.WREG 4
def W5  (s : State) : BitVec 32 := s.WREG 5
def W6  (s : State) : BitVec 32 := s.WREG 6
def W7  (s : State) : BitVec 32 := s.WREG 7
def W8  (s : State) : BitVec 32 := s.WREG 8
def W9  (s : State) : BitVec 32 := s.WREG 9
def W10 (s : State) : BitVec 32 := s.WREG 10
def W11 (s : State) : BitVec 32 := s.WREG 11
def W12 (s : State) : BitVec 32 := s.WREG 12
def W13 (s : State) : BitVec 32 := s.WREG 13
def W14 (s : State) : BitVec 32 := s.WREG 14
def W15 (s : State) : BitVec 32 := s.WREG 15
def W16 (s : State) : BitVec 32 := s.WREG 16
def W17 (s : State) : BitVec 32 := s.WREG 17
def W18 (s : State) : BitVec 32 := s.WREG 18
def W19 (s : State) : BitVec 32 := s.WREG 19
def W20 (s : State) : BitVec 32 := s.WREG 20
def W21 (s : State) : BitVec 32 := s.WREG 21
def W22 (s : State) : BitVec 32 := s.WREG 22
def W23 (s : State) : BitVec 32 := s.WREG 23
def W24 (s : State) : BitVec 32 := s.WREG 24
def W25 (s : State) : BitVec 32 := s.WREG 25
def W26 (s : State) : BitVec 32 := s.WREG 26
def W27 (s : State) : BitVec 32 := s.WREG 27
def W28 (s : State) : BitVec 32 := s.WREG 28
def W29 (s : State) : BitVec 32 := s.WREG 29
def W30 (s : State) : BitVec 32 := s.WREG 30

theorem WREG31_zero (s : State) : s.WREG 31 = 0 := by
  rfl

def WSP (s : State) : BitVec 32 :=
  s.SP.truncate 32

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

def shift (st : ShiftType) (sa : BitVec 6) {n : Nat} (bv : BitVec n) :
    BitVec n :=
  match st with
  | .LSL => bv.shiftLeft sa.toNat
  | .LSR => bv.ushiftRight sa.toNat
  | .ASR => bv.sshiftRight sa.toNat
  | .ROR => bv.rotateRight sa.toNat

end ShiftType

/--
Extended register operands.
-/
inductive ExtendedType where
  | UXTB
  | UXTH
  | UXTW
  | UXTX
  | SXTH
  | SXTW
  | SXTX
deriving DecidableEq, Repr

namespace State

/-- The main SIMD registers. -/
def QREG (s : State) (n : Nat) : BitVec 128 :=
  s.simdregisters n

def DREG (s : State) (n : Nat) : BitVec 64 :=
  (s.QREG n).truncate 64

def SREG (s : State) (n : Nat) : BitVec 32 :=
  (s.DREG n).truncate 32

def HREG (s : State) (n : Nat) : BitVec 16 :=
  (s.SREG n).truncate 16

def BREG (s : State) (n : Nat) : BitVec 8 :=
  (s.HREG n).truncate 8

def Q0  (s : State) : BitVec 128 := s.QREG 0
def Q1  (s : State) : BitVec 128 := s.QREG 1
def Q2  (s : State) : BitVec 128 := s.QREG 2
def Q3  (s : State) : BitVec 128 := s.QREG 3
def Q4  (s : State) : BitVec 128 := s.QREG 4
def Q5  (s : State) : BitVec 128 := s.QREG 5
def Q6  (s : State) : BitVec 128 := s.QREG 6
def Q7  (s : State) : BitVec 128 := s.QREG 7
def Q8  (s : State) : BitVec 128 := s.QREG 8
def Q9  (s : State) : BitVec 128 := s.QREG 9
def Q10 (s : State) : BitVec 128 := s.QREG 10
def Q11 (s : State) : BitVec 128 := s.QREG 11
def Q12 (s : State) : BitVec 128 := s.QREG 12
def Q13 (s : State) : BitVec 128 := s.QREG 13
def Q14 (s : State) : BitVec 128 := s.QREG 14
def Q15 (s : State) : BitVec 128 := s.QREG 15
def Q16 (s : State) : BitVec 128 := s.QREG 16
def Q17 (s : State) : BitVec 128 := s.QREG 17
def Q18 (s : State) : BitVec 128 := s.QREG 18
def Q19 (s : State) : BitVec 128 := s.QREG 19
def Q20 (s : State) : BitVec 128 := s.QREG 20
def Q21 (s : State) : BitVec 128 := s.QREG 21
def Q22 (s : State) : BitVec 128 := s.QREG 22
def Q23 (s : State) : BitVec 128 := s.QREG 23
def Q24 (s : State) : BitVec 128 := s.QREG 24
def Q25 (s : State) : BitVec 128 := s.QREG 25
def Q26 (s : State) : BitVec 128 := s.QREG 26
def Q27 (s : State) : BitVec 128 := s.QREG 27
def Q28 (s : State) : BitVec 128 := s.QREG 28
def Q29 (s : State) : BitVec 128 := s.QREG 29
def Q30 (s : State) : BitVec 128 := s.QREG 30
def Q31 (s : State) : BitVec 128 := s.QREG 31

def D0  (s : State) : BitVec 64 := s.DREG 0
def D1  (s : State) : BitVec 64 := s.DREG 1
def D2  (s : State) : BitVec 64 := s.DREG 2
def D3  (s : State) : BitVec 64 := s.DREG 3
def D4  (s : State) : BitVec 64 := s.DREG 4
def D5  (s : State) : BitVec 64 := s.DREG 5
def D6  (s : State) : BitVec 64 := s.DREG 6
def D7  (s : State) : BitVec 64 := s.DREG 7
def D8  (s : State) : BitVec 64 := s.DREG 8
def D9  (s : State) : BitVec 64 := s.DREG 9
def D10 (s : State) : BitVec 64 := s.DREG 10
def D11 (s : State) : BitVec 64 := s.DREG 11
def D12 (s : State) : BitVec 64 := s.DREG 12
def D13 (s : State) : BitVec 64 := s.DREG 13
def D14 (s : State) : BitVec 64 := s.DREG 14
def D15 (s : State) : BitVec 64 := s.DREG 15
def D16 (s : State) : BitVec 64 := s.DREG 16
def D17 (s : State) : BitVec 64 := s.DREG 17
def D18 (s : State) : BitVec 64 := s.DREG 18
def D19 (s : State) : BitVec 64 := s.DREG 19
def D20 (s : State) : BitVec 64 := s.DREG 20
def D21 (s : State) : BitVec 64 := s.DREG 21
def D22 (s : State) : BitVec 64 := s.DREG 22
def D23 (s : State) : BitVec 64 := s.DREG 23
def D24 (s : State) : BitVec 64 := s.DREG 24
def D25 (s : State) : BitVec 64 := s.DREG 25
def D26 (s : State) : BitVec 64 := s.DREG 26
def D27 (s : State) : BitVec 64 := s.DREG 27
def D28 (s : State) : BitVec 64 := s.DREG 28
def D29 (s : State) : BitVec 64 := s.DREG 29
def D30 (s : State) : BitVec 64 := s.DREG 30
def D31 (s : State) : BitVec 64 := s.DREG 31

theorem zero_register (s : State) {n : Nat} :
    s.ZR = 0#n ∧ s.XZR = 0 ∧ s.XREG 31 = 0 ∧ s.WZR = 0 ∧ s.WREG 31 = 0 := by
  simp [s.ZR_zero, s.XZR_zero, s.XREG31_zero, s.WZR_zero, s.WREG31_zero]

theorem XZR_ZR (s : State) : s.XZR = s.ZR := by
  rewrite [s.XZR_zero, s.ZR_zero]; rfl

theorem WZR_ZR (s : State) : s.WZR = s.ZR := by
  rewrite [s.WZR_zero, s.ZR_zero]; rfl

end State

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

def State.condition (s : State) : Condition → Bool
  | .EQ => s.ZF
  | .NE => !s.ZF
  | .CS => s.CF
  | .CC => !s.CF
  | .MI => s.NF
  | .PL => !s.NF
  | .VS => s.VF
  | .VC => !s.VF
  | .HI => s.CF && !s.ZF
  | .LS => !(s.CF && !s.ZF)
  | .GE => s.NF == s.VF
  | .LT => !(s.NF == s.VF)
  | .GT => !s.ZF && (s.NF == s.VF)
  | .LE => !(!s.ZF && (s.NF == s.VF))
  | .AL => true
  | .NV => true

end Bignum.ArmRev
