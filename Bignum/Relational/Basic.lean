/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Bignum.Component

@[expose] public section

/-! # Relational model of programs and Hoare-type rules -/

namespace Bignum.Relational

universe u₁ u₂ u₃ u₄

variable {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄}

/--
Composition of relations (sequencing).
-/
def seq (r₁ : α → β → Prop) (r₂ : β → γ → Prop) : α → γ → Prop :=
  fun a c ↦ ∃ b, r₁ a b ∧ r₂ b c

@[inherit_doc] infixr:62 " ,, " => seq

/--
Subsumption of relations.
-/
def subsumed (r r' : α → β → Prop) : Prop :=
  ∀ a b, r a b → r' a b

@[inherit_doc] infixr:50 " ⊑ " => subsumed

/--
Assignment of component as a (functional) relation.
-/
def assign (cp : Component α β) (b : β) : α → α → Prop :=
  fun a a' ↦ cp.write b a = a'

@[inherit_doc] infixr:70 " ≔ " => assign

end Bignum.Relational
