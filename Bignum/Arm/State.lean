/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Bignum.Arm.Condition
public import Bignum.BitVec
public import Bignum.Component
public import Bignum.Memory
public import Bignum.Relational
public import Bignum.Safety

@[expose] public section

/-! # The ARM (aarch64) state -/

namespace Bignum.Arm

universe u

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
  _memory : Memory 64

  /-- Observable uarch events. -/
  _events : List (UArchEvent 64)

namespace State

/-- The all zeros state. -/
def allZeros : State := {
  _PC            := 0
  _registers     := fun _ ↦ 0
  _simdregisters := fun _ ↦ 0
  _flags         := 0
  _memory        := .allZeros
  _events        := []
}

/-- The all ones state. -/
def allOnes : State := {
  _PC            := .allOnes 64
  _registers     := fun _ ↦ .allOnes 64
  _simdregisters := fun _ ↦ .allOnes 128
  _flags         := .allOnes 4
  _memory        := .allOnes
  _events        := []
}

instance : Inhabited State where
  default := allZeros

/-- Reads from state component. -/
def read (s : State) {α : Type u} (cp : Component State α) : α :=
  cp.read s

/-- Writes to state component. -/
def write (s : State) {α : Type u} (cp : Component State α) (a : α) : State :=
  cp.write a s

end State

/-! ## Basic components -/

/-- Program counter. -/
def PC : Component State (BitVec 64) :=
  ⟨fun s ↦ s._PC, fun x s ↦ {s with _PC := x}⟩

/-- General-purpose registers. -/
def registers : Component State (BitVec 5 → BitVec 64) :=
  ⟨fun s ↦ s._registers, fun x s ↦ {s with _registers := x}⟩

/-- SIMD registers. -/
def simdregisters : Component State (BitVec 5 → BitVec 128) :=
  ⟨fun s ↦ s._simdregisters, fun x s ↦ {s with _simdregisters := x}⟩

/-- NZCV flags. -/
def flags : Component State (BitVec 4) :=
  ⟨fun s ↦ s._flags, fun x s ↦ {s with _flags := x}⟩

/-- Byte-addressable memory. -/
def memory : Component State (Memory 64) :=
  ⟨fun s ↦ s._memory, fun x s ↦ {s with _memory := x}⟩

/-- Observable micro-architectural events. -/
def events : Component State (List (UArchEvent 64)) :=
  ⟨fun s ↦ s._events, fun x s ↦ {s with _events := x}⟩

/-- Negative condition flag. -/
def NF : Component State Bool :=
  flags :> .bitelement 3

/-- Zero condition flag. -/
def ZF : Component State Bool :=
  flags :> .bitelement 2

/-- Carry condition flag. -/
def CF : Component State Bool :=
  flags :> .bitelement 1

/-- Overflow condition flag. -/
def VF : Component State Bool :=
  flags :> .bitelement 0

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

/-- Zero register: zero as source, ignored as destination. -/
def XZR : Component State (BitVec 64) :=
  .rvalue 0#64

/-- Bottom 32-bits of the zero register (ignored as destination). -/
def WZR : Component State (BitVec 32) :=
  XZR :> .bottom32

/-- Generic version of XZR. -/
def ZR {w : Nat} : Component State (BitVec w) :=
  .rvalue 0

/-- Main register `n`. -/
def XREG (n : Nat) : Component State (BitVec 64) :=
  if n ≥ 31 then XZR else registers :> .element n

/-- Zero-topped lower 32-bit version of main register `n`. -/
def WREG (n : Nat) : Component State (BitVec 32) :=
  XREG n :> .zerotop32

/-- Stack pointer. -/
def SP := registers :> .element 31

/-- Zero-topped lower 32-bit version of stack pointer. -/
def WSP := SP :> .zerotop32

/-- SIMD register `n`. -/
def QREG (n : Nat) : Component State (BitVec 128) :=
  simdregisters :> .element n

/-- Zero-topped lower 64-bit version of SIMD register `n`. -/
def DREG (n : Nat) : Component State (BitVec 64) :=
  QREG n :> .zerotop64

/-- Zero-topped lower 32-bit version of SIMD register `n`. -/
def SREG (n : Nat) : Component State (BitVec 32) :=
  DREG n :> .zerotop32

/-- Zero-topped lower 16-bit version of SIMD register `n`. -/
def HREG (n : Nat) : Component State (BitVec 16) :=
  SREG n :> .zerotop16

/-- Zero-topped lower 8-bit version of SIMD register `n`. -/
def BREG (n : Nat) : Component State (BitVec 8) :=
  HREG n :> .zerotop8

/--
SIMD lane replicating the `i`th double twice (write is no-op).
-/
def LANE_D (i : Nat) : Component (BitVec 128) (BitVec 128) :=
  .through (λ bv ↦ .replicate 2 (bv.extractLsb' (64 * i) 64)) id

/--
SIMD lane replicating the `i`th word four times (write is no-op).
-/
def LANE_S (i : Nat) : Component (BitVec 128) (BitVec 128) :=
  .through (λ bv ↦ .replicate 4 (bv.extractLsb' (32 * i) 32)) id

/--
SIMD lane replicating the `i`th half-word 8 times (write is no-op).
-/
def LANE_H (i : Nat) : Component (BitVec 128) (BitVec 128) :=
  .through (λ bv ↦ .replicate 8 (bv.extractLsb' (16 * i) 16)) id

/--
SIMD lane replicating the `i`th byte 16 times (write is no-op).
-/
def LANE_B (i : Nat) : Component (BitVec 128) (BitVec 128) :=
  .through (λ bv ↦ .replicate 16 (bv.extractLsb' (8 * i) 8)) id

/-! ## Memory -/

/-- Multi-byte chunk of memory (little-endian). -/
def bytes (addr : BitVec 64) (len : Nat) :
    Component State ByteList :=
  memory :> .bytesLE addr len

namespace State

/-- Tests whether `bs` is loaded on memory at 4-byte aligned `addr`. -/
def alignedBytesLoaded
    (s : State) (addr : BitVec 64) (bs : ByteList) : Bool :=
  s._memory.alignedBytesLoadedLE addr bs

/-- Asserts that `bs` is loaded on memory at 4-byte aligned `addr`. -/
def AlignedBytesLoaded
    (s : State) (addr : BitVec 64) (bs : ByteList) : Prop :=
  s._memory.AlignedBytesLoadedLE addr bs

theorem alignedBytesLoaded_iff
    (s : State) (addr : BitVec 64) (bs : ByteList) :
    s.alignedBytesLoaded addr bs ↔
    s.AlignedBytesLoaded addr bs := by
  rw [alignedBytesLoaded, AlignedBytesLoaded,
    Memory.alignedBytesLoadedLE_iff]

instance (s : State) (addr : BitVec 64) (bs : ByteList) :
    Decidable (AlignedBytesLoaded s addr bs) :=
  decidable_of_iff (s.alignedBytesLoaded addr bs)
    (s.alignedBytesLoaded_iff addr bs)

end State
end Bignum.Arm
