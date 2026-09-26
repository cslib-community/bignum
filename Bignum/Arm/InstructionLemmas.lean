/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Guilherme Lima
-/
module

public import Bignum.Arm.Instruction

@[expose] public section

/-! # Theorems about ARM state -/

set_option autoImplicit false

namespace Bignum.Arm.State

/-! ## Registers -/

theorem XZR_zero : XZR = .rvalue 0 := by
  rfl

theorem WZR_zero : WZR = .rvalue 0 := by
  rfl

theorem ZR_zero (w : Nat) : @ZR w = .rvalue 0 := by
  rfl

theorem XREG31_zero : XREG 31 = .rvalue 0 := by
  rfl

theorem WREG31_zero : WREG 31 = .rvalue 0 := by
  rfl

theorem zero_register {n : Nat} : @ZR n = (.rvalue 0) ∧
    XZR = (.rvalue 0) ∧ XREG 31 = (.rvalue 0) ∧
    WZR = (.rvalue 0) ∧ WREG 31 = (.rvalue 0) := by
  simp [ZR_zero, XZR_zero, XREG31_zero, WZR_zero, WREG31_zero]

theorem XZR_ZR : XZR = ZR := by
  rw [XZR_zero, ZR_zero]

theorem WZR_ZR : WZR = ZR := by
  rw [WZR_zero, ZR_zero]

theorem shifted_LSL_zero {w : Nat} (reg : Component State (BitVec w)) :
    shifted .LSL 0 reg = reg := by
  simp [shifted]

theorem shifted_LSR_zero {w : Nat} (reg : Component State (BitVec w)) :
    shifted .LSR 0 reg = reg := by
  simp [shifted]

theorem shifted_ASR_zero {w : Nat} (reg : Component State (BitVec w)) :
    shifted .ASR 0  reg = reg := by
  simp [shifted]

theorem shifted_ROR_zero {w : Nat} (reg : Component State (BitVec w)) :
    shifted .ROR 0  reg = reg := by
  simp [shifted, BitVec.rotateRight_def]

/-! ## Condition codes -/

namespace Condition

theorem invert_ofBitVec_toBitVec_xor (c : Condition) :
    c.invert = Condition.ofBitVec (c.toBitVec.xor 1) := by
  cases c <;> simp [ofBitVec, toBitVec, invert]

theorem invert_involutive (c : Condition) :
    c.invert.invert = c := by
  cases c <;> simp [invert]

end Condition

theorem condition_EQ (s : State) :
    s.condition .EQ = ZF.read s := by rfl

theorem condition_NE (s : State) :
    s.condition .NE = !ZF.read s := by rfl

theorem condition_CS (s : State) :
    s.condition .CS = CF.read s := by rfl

theorem condition_HS (s : State) :
    s.condition .HS = CF.read s := by rfl

theorem condition_CC (s : State) :
    s.condition .CC = !CF.read s := by rfl

theorem condition_LO (s : State) :
    s.condition .LO = !CF.read s := by rfl

theorem condition_MI (s : State) :
    s.condition .MI = NF.read s := by rfl

theorem condition_PL (s : State) :
    s.condition .PL = !NF.read s := by rfl

theorem condition_VS (s : State) :
    s.condition .VS = VF.read s := by rfl

theorem condition_VC (s : State) :
    s.condition .VC = !VF.read s := by rfl

theorem condition_HI (s : State) :
    s.condition .HI = (CF.read s && !ZF.read s) := by rfl

theorem condition_LS (s : State) :
    s.condition .LS = !(CF.read s && !ZF.read s) := by rfl

theorem condition_GE (s : State) :
    s.condition .GE = (NF.read s == VF.read s) := by rfl

theorem condition_LT (s : State) :
    s.condition .LT = !(NF.read s == VF.read s) := by rfl

theorem condition_GT (s : State) :
    s.condition .GT = (!ZF.read s && (NF.read s == VF.read s)) := by rfl

theorem condition_LE (s : State) :
    s.condition .LE = !(!ZF.read s && (NF.read s == VF.read s)) := by rfl

theorem condition_AL (s : State) :
    s.condition .AL = true := by rfl

theorem condition_NV (s : State) :
    s.condition .NV = true := by rfl

end Bignum.Arm.State
