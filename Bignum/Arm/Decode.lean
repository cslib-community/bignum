/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Bignum.Arm.Instruction
import Bignum.Arm.State
import Bignum.BitVec

@[expose] public section

/-! # ARM instruction decoding -/

namespace Bignum.Arm.Decode

universe u

/--
`XREG` allowing direct access to `SP`.
-/
def XREG_SP (x : BitVec 5) :=
  registers :> .element x

/--
`WREG` variant allowing direct access to `WSP`.
-/
def WREG_SP (x : BitVec 5) :=
  XREG_SP x :> .zerotop32

/--
Calls ADD/SUB or ADDS/SUBS.
-/
def addOp (op : Bool) (S : Bool) {w : Nat} :
    Component State (BitVec w) →
    Component State (BitVec w) →
    Component State (BitVec w) → State → State → Prop :=
  if op then if S then SUBS else SUB
        else if S then ADDS else ADD

/--
Decodes the 4-byte word `x`.
-/
def decode (x : BitVec 32) : Option (Rel State State) :=
  match_bv x with
  -- ADD(S)/SUB(S) (immediate)
  | [sf:1, op:1, S:1, 100010, sh:1, imm12:12, Rn:5, Rd:5] =>
    let val := if sh then imm12.toNat <<< 12 else imm12.toNat
    some (if sf
      then addOp op S (if S then XREG Rd else XREG_SP Rd)
        (XREG_SP Rn) (.rvalue val)
      else addOp op S (if S then WREG Rd else WREG_SP Rd)
        (WREG_SP Rn) (.rvalue val))
  | _ => none

end Bignum.Arm.Decode
