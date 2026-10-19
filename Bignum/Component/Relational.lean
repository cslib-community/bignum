/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Bignum.Component.Basic

@[expose] public section

/-! # Relational model of programs and Hoare-type rules -/

namespace Bignum.Component

universe u₁ u₂ u₃ u₄

variable {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄}

/--
Composition of relations (sequencing).
-/
def Seq (r₁ : α → β → Prop) (r₂ : β → γ → Prop) : α → γ → Prop :=
  fun a c ↦ ∃ b, r₁ a b ∧ r₂ b c

@[inherit_doc] infixr:62 " ,, " => Seq

/--
Subsumption of relations.
-/
def Subsumed (r r' : α → β → Prop) : Prop :=
  ∀ a b, r a b → r' a b

@[inherit_doc] infixr:50 " ⊑ " => Subsumed

/--
Assignment of component as a functional relation.
-/
def Assign (cp : Component α β) (b : β) : α → α → Prop :=
  fun a a' ↦ cp.write b a = a'

@[inherit_doc] infixr:70 " ≔ " => Assign

/--
Non-deterministic assignment of component.
-/
def Assigns (cp : Component α β) : α → α → Prop :=
  fun a a' ↦ ∃ b, (cp ≔ b) a a'

end Bignum.Component
