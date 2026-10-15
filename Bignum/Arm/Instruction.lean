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

/-! ## General register-register instructions -/

/-- Adds `Rm` and `Rn` and writes the result to `Rd`. -/
def ADD {α : Type u} {w : Nat}
    (Rd : Component α (BitVec w))
    (Rm : Component α (BitVec w))
    (Rn : Component α (BitVec w))
    (s : α) : α → Prop :=
  let m := Rm.read s
  let n := Rn.read s
  let d : BitVec w := m + n
  (Rd ≔ d) s

/-- Subtracts `Rm` from `Rn` and writes the result to `Rd`. -/
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
