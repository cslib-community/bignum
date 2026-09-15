/-
Copyright (c) 2026 Guilherme Lima. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Guilherme Lima
-/

module

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
  PC : BitVec 64

  /-- 31 general purpose registers (0-30) plus SP (register 31). -/
  registers : BitVec 5 → BitVec 64

  /-- 32 SIMD registers. -/
  simdregisters : BitVec 5 → BitVec 128

  /-- NZCV flags. -/
  flags : BitVec 4

  /-- Byte-addressable memory with 64-bit address space. -/
  memory : BitVec 64 -> BitVec 8

  /-- Observable uarch events. -/
  events : List UArchEvent

namespace State

/-- The all zeros state. -/
def allZeros : State := {
  PC            := 0
  registers     := λ _ ↦ 0
  simdregisters := λ _ ↦ 0
  flags         := 0
  memory        := λ _ ↦ 0
  events        := []
}

/-- The all ones state. -/
def allOnes : State := {
  PC            := BitVec.allOnes 64
  registers     := λ _ ↦ BitVec.allOnes 64
  simdregisters := λ _ ↦ BitVec.allOnes 128
  flags         := BitVec.allOnes 4
  memory        := λ _ ↦ BitVec.allOnes 8,
  events        := []
}

instance : Inhabited State where
  default := allZeros

/-- The negative condition flag. -/
def NF (s : State) : Bool :=
  s.flags.getLsb 3

/-- The zero condition flag. -/
def ZF (s : State) : Bool :=
  s.flags.getLsb 2

/-- The carry condition flag. -/
def CF (s : State) : Bool :=
  s.flags.getLsb 1

/-- The overflow condition flag. -/
def VF (s : State) : Bool :=
  s.flags.getLsb 0

/-- The zero register: zero as source, ignored as destination. -/
def XZR (_ : State) : BitVec 64 :=
  0

@[simp]
theorem XZR_zero (s : State) : s.XZR = 0 := by
  rfl

/-- Main integer registers. -/
def XREG (s : State) (n : Nat) : BitVec 64 :=
  if n ≤ 31 then s.registers n else s.XZR

theorem XREG_eq_zero_of_n_gt_31 (s : State) (n : Nat) :
    n > 31 → s.XREG n = 0 := by
  simp [XREG]; intro h _
  have _ := Nat.not_le_of_gt h; contradiction

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

/-- Stack pointer. --/
def SP (s : State) : BitVec 64 :=
  s.XREG 31

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
def WSP (s : State) : BitVec 32 := s.WREG 31

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

def shift {n : Nat} (bv : BitVec n) (st : ShiftType) (sa : BitVec 6) :
    BitVec n :=
  match st with
    | .LSL => bv.shiftLeft sa.toNat
    | .LSR => bv.ushiftRight sa.toNat
    | .ASR => bv.sshiftRight sa.toNat
    | .ROR => bv.rotateRight sa.toNat

end ShiftType

end Bignum.ArmRev
