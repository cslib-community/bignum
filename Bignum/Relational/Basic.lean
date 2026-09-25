/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Guilherme Lima
-/
module

@[expose] public section

/-! # Lemmas about relations and Hoare-type rules -/

set_option autoImplicit false

namespace Bignum.Relational

universe u₁ u₂ u₃ u₄

variable {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄}

/--
Composition of relations (stands for sequencing).
-/
def seq (r₁ : α → β → Prop) (r₂ : β → γ → Prop) : α → γ → Prop :=
  λ a c ↦ ∃ b, r₁ a b ∧ r₂ b c

infixr:62 " ,, " => seq

end Bignum.Relational
