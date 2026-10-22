/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Bignum.Arm.Instruction
public import Bignum.Arm.State
public import Bignum.BitVec

@[expose] public section

/-! # ARM instruction decoding -/

namespace Bignum.Arm.Decode

universe u

def XREG_SP (x : BitVec 5) := registers :> .element x
def WREG_SP (x : BitVec 5) := XREG_SP x :> .zerotop32
def XREG' (x : BitVec 5) := XREG x.toNat
def WREG' (x : BitVec 5) := WREG x.toNat
def QREG' (x : BitVec 5) := QREG x.toNat
def DREG' (x : BitVec 5) := DREG x.toNat

def addOp (op : Bool) (S : Bool) {α : Type u} {w : Nat} :
    Component α (BitVec w) →
    Component α (BitVec w) →
    Component α (BitVec w) → α → α → Prop :=
  if op then if S then panic! "not implemented" else @SUB α w
        else if S then panic! "not implemented" else @ADD α w

/--
Decodes the 4-byte word `x`.
-/
def decode (x : BitVec 32) : Option (Relation State State) :=
  match_bv x with
  | [sf:1, op:1, S:1, 100010, sh:1, imm12:12, Rn:5, Rd:5] =>
    let val := if sh then imm12.toNat <<< 12 else imm12.toNat
    some (if sf
      then Decode.addOp op S (if S then XREG' Rd else XREG_SP Rd)
        (XREG_SP Rn) (.rvalue val)
      else addOp op S (if S then WREG' Rd else WREG_SP Rd)
        (WREG_SP Rn) (.rvalue val))
  | _ => none

end Bignum.Arm.Decode
