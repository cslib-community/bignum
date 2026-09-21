/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Guilherme Lima
-/
module

public import Bignum.BitVec
public import Bignum.Component

@[expose] public section

set_option autoImplicit false

namespace Bignum.Component

/-- Component for a bit within a BitVec. -/
def bitelement {w : Nat} (i : Fin w) : Component (BitVec w) Bool :=
  ⟨λ bv ↦ bv.getLsb i, λ b bv ↦ BitVec.setLsb bv i b⟩

end Bignum.Component
