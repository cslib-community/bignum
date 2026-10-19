/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

@[expose] public section

/-! # Operations on binary relations -/

namespace Bignum

universe u v

/-- Binary relation -/
abbrev Relation (α : Type u) (β : Type v) := α → β → Prop

namespace Relation

universe u₁ u₂ u₃ u₄

variable {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄}

/--
Composition of relations (sequencing).
-/
def Seq (r₁ : Relation α β) (r₂ : Relation β γ) : Relation α γ :=
  fun a c ↦ ∃ b, r₁ a b ∧ r₂ b c

/--
Subsumption of relations.
-/
def Subsumed (r r' : Relation α β) : Prop :=
  ∀ a b, r a b → r' a b

end Relation

@[inherit_doc] scoped infixr:62 " ,, " => Relation.Seq
@[inherit_doc] scoped infixr:50 " ⊑ " => Relation.Subsumed

end Bignum
