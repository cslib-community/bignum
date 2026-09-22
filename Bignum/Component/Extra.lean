/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Guilherme Lima
-/
module

public import Bignum.BitVec
public import Bignum.Component.Basic

@[expose] public section

set_option autoImplicit false

namespace Bignum.Component

/-- Component for a bit within a bitvector. -/
def bitelement {w : Nat} (i : Fin w) : Component (BitVec w) Bool :=
  ⟨λ bv ↦ bv.getLsb i, λ b bv ↦ BitVec.setLsb bv i b⟩

/-- Component for subwords of a bitvector. -/
def subword {w : Nat} (start len : Nat) :
    Component (BitVec w) (BitVec len) :=
  ⟨BitVec.extractLsb' start len, λ b bv ↦ bv.overwriteLsb' start len b⟩

end Bignum.Component
