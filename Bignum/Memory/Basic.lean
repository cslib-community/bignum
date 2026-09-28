/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Guilherme Lima
-/
module

public import Bignum.Component

@[expose] public section

/-! # Predicates for loading code into memory -/

set_option autoImplicit false

namespace Bignum.Memory

universe u₁ u₂ u₃ u₄

variable {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄}
variable (memory : Component α (BitVec 64 → BitVec 8))

-- def bytes_loaded

end Bignum.Memory
