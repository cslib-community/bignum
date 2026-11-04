/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Bignum.Arm.Abbrev
public import Bignum.Arm.State

@[expose] public section

/-! # ARM instructions -/

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

/--
Adds with carry.
-/
def ADC {w : Nat}
    (Rd : Component State (BitVec w))
    (Rm : Component State (BitVec w))
    (Rn : Component State (BitVec w))
    (s : State) : State → Prop :=
  let m := Rm.read s
  let n := Rn.read s
  let c := if CF.read s then 1#w else 0#w
  let d : BitVec w := m + n + c
  (Rd ≔ d) s

/--
Adds with carry, setting flags.
-/
def ADCS {w : Nat}
    (Rd : Component State (BitVec w))
    (Rm : Component State (BitVec w))
    (Rn : Component State (BitVec w))
    (s : State) : State → Prop :=
  let m := Rm.read s
  let n := Rn.read s
  let c := if CF.read s then 1#w else 0#w
  let d : BitVec w := m + n + c
  (Rd ≔ d ,,
   NF ≔ (d.toInt < 0) ,,
   ZF ≔ (d = 0) ,,
   CF ≔ (m.toNat + n.toNat ≠ d.toNat) ,,
   VF ≔ (m.toInt + n.toInt ≠ d.toInt)) s

/--
Adds `Rm` and `Rn` and writes the result to `Rd`.
-/
def ADD {w : Nat}
    (Rd : Component State (BitVec w))
    (Rm : Component State (BitVec w))
    (Rn : Component State (BitVec w))
    (s : State) : State → Prop :=
  let m := Rm.read s
  let n := Rn.read s
  let d : BitVec w := m + n
  (Rd ≔ d) s

/--
Add, setting flags.
-/
def ADDS {w : Nat}
    (Rd : Component State (BitVec w))
    (Rm : Component State (BitVec w))
    (Rn : Component State (BitVec w))
    (s : State) : State → Prop :=
  let m := Rm.read s
  let n := Rn.read s
  let d : BitVec w := m + n
  (Rd ≔ d ,,
   NF ≔ (d.toInt < 0) ,,
   ZF ≔ (d = 0) ,,
   CF ≔ (m.toNat + n.toNat ≠ d.toNat) ,,
   VF ≔ (m.toInt + n.toInt ≠ d.toInt)) s

/--
Subtract with carry.
-/
def SBC {w : Nat}
    (Rd : Component State (BitVec w))
    (Rm : Component State (BitVec w))
    (Rn : Component State (BitVec w))
    (s : State) : State → Prop :=
  let m := Rm.read s
  let n := Rn.read s
  let c := if CF.read s then 0#w else 1#w
  let d : BitVec w := m - (n + c)
  (Rd ≔ d) s

/--
Subtracts with carry, setting flags.
-/
def SBCS {w : Nat}
    (Rd : Component State (BitVec w))
    (Rm : Component State (BitVec w))
    (Rn : Component State (BitVec w))
    (s : State) : State → Prop :=
  let m := Rm.read s
  let n := Rn.read s
  let c := if CF.read s then 0#w else 1#w
  let d : BitVec w := m - (n + c)
  (Rd ≔ d ,,
   NF ≔ (d.toInt < 0) ,,
   ZF ≔ (d = 0) ,,
   CF ≔ (m.toNat - (n.toNat + c) = d.toNat) ,,
   VF ≔ (m.toInt - (n.toInt + c) ≠ d.toInt)) s

/--
Subtracts `Rm` from `Rn` and writes the result to `Rd`.
-/
def SUB {w : Nat}
    (Rd : Component State (BitVec w))
    (Rm : Component State (BitVec w))
    (Rn : Component State (BitVec w))
    (s : State) : State → Prop :=
  let m := Rm.read s
  let n := Rn.read s
  let d : BitVec w := m - n
  (Rd ≔ d) s

/--
Sub, settings flags.
-/
def SUBS {w : Nat}
    (Rd : Component State (BitVec w))
    (Rm : Component State (BitVec w))
    (Rn : Component State (BitVec w))
    (s : State) : State → Prop :=
  let m := Rm.read s
  let n := Rn.read s
  let d : BitVec w := m - n
  (Rd ≔ d ,,
   NF ≔ (d.toInt < 0) ,,
   ZF ≔ (d = 0) ,,
   CF ≔ (m.toNat - n.toNat = d.toNat) ,,
   VF ≔ (m.toInt - n.toInt ≠ d.toInt)) s

end Bignum.Arm
