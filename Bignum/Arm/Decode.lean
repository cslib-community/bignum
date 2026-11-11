/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Bignum.Arm.Component
public import Bignum.Arm.Instruction
public import Bignum.Arm.State
public import Bignum.BitVec

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
Calls ADC/SBC or ADCS/SBCS.
-/
def adcOp (op : Bool) (S : Bool) {w : Nat} :
    Component State (BitVec w) →
    Component State (BitVec w) →
    Component State (BitVec w) →
    State → State → Prop :=
  if op then if S then SBCS else SBC
        else if S then ADCS else ADC

/--
Calls ADD/SUB or ADDS/SUBS.
-/
def addOp (op : Bool) (S : Bool) {w : Nat} :
    Component State (BitVec w) →
    Component State (BitVec w) →
    Component State (BitVec w) →
    State → State → Prop :=
  if op then if S then SUBS else SUB
        else if S then ADDS else ADD

/--
Interprets `data` as a 4-byte encoded instruction and attempts to decode it.
Returns there resulting instruction if successful.
-/
def decode (data : BitVec 32) : Option (Rel State State) :=
  match_bv data with
  -- ADC(S)/SBC(S)
  | [sf:1, op:1, S:1, 11010000, Rm:5, 000000, Rn:5, Rd:5] =>
    some (if sf then adcOp op S (XREG Rd) (XREG Rn) (XREG Rm)
                else adcOp op S (WREG Rd) (WREG Rn) (WREG Rm))
  -- ADD(S)/SUB(S) (immediate)
  | [sf:1, op:1, S:1, 100010, sh:1, imm12:12, Rn:5, Rd:5] =>
    let val := if sh then imm12.toNat <<< 12 else imm12.toNat
    some (if sf
      then addOp op S (if S then XREG Rd else XREG_SP Rd)
        (XREG_SP Rn) (.rvalue val)
      else addOp op S (if S then WREG Rd else WREG_SP Rd)
        (WREG_SP Rn) (.rvalue val))
  -- ADD(S)/SUB(S) (shifted register)
  | [sf:1, op:1, S:1, 01011, sty:2, 0, Rm:5, sam:6, Rn:5, Rd:5] =>
    if sty = 0b11 then
      none
    else if sf then
       some (addOp op S (XREG Rd) (XREG Rn)
         ((XREG Rm).shifted sty sam.toNat))
    else if sam < 32 then
       some (addOp op S (WREG Rd) (WREG Rn)
         ((WREG Rm).shifted sty sam.toNat))
    else
      none
  | _ => none

end Bignum.Arm.Decode
