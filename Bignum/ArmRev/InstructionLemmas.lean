/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Guilherme Lima
-/
module

public import Bignum.ArmRev.Instruction

@[expose] public section

set_option autoImplicit false

namespace Bignum.ArmRev.State

theorem XZR_zero : XZR = Component.rvalue 0 := by
  rfl

theorem WZR_zero : WZR = Component.rvalue 0 := by
  rfl

theorem ZR_zero (w : Nat) : @ZR w = Component.rvalue 0 := by
  rfl

theorem XREG31_zero : XREG 31 = Component.rvalue 0 := by
  rfl

end Bignum.ArmRev.State
