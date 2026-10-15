/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Bignum.Arm.Operand
public import Bignum.Arm.State

@[expose] public section

/-! # ARM-specific components -/

namespace Bignum.Component

/--
Shifted version of register `reg` (writes are no-ops).
-/
def shifted {n : Nat} (reg : Component Arm.State (BitVec n))
    (sty : Arm.ShiftType) (sa : Nat) : Component Arm.State (BitVec n) :=
  ⟨fun s ↦ sty.shift sa (Component.read reg s), Component.write reg⟩

/--
Extended version of register `reg` (writes are undefined).
-/
def extended {n : Nat} (reg : Component Arm.State (BitVec n))
    (xty : Arm.ExtendedType) {m : Nat} : Component Arm.State (BitVec m) :=
  -- We use `default` as a substitute for HOL Light's ARB (arbitrary).
  ⟨fun s ↦ xty.extend (Component.read reg s), default⟩

end Bignum.Component
