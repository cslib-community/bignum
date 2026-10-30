/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

@[expose] public section

/-! # Relational model of programs and Hoare-rules -/

namespace Bignum

universe u v w

/-- Predicate (unary relation). -/
abbrev Set (α : Type u) := α → Prop

namespace Set

variable {α : Type u}

/--
The empty predicate.
-/
def Empty : α → Prop :=
  fun _ ↦ False

instance : EmptyCollection (Set α) where
  emptyCollection := Empty

/--
The full predicate.
-/
def Full : α → Prop :=
  fun _ ↦ True

instance : HasSubset (Set α) where
  Subset p q := ∀ ⦃a⦄, p a → q a

instance : Union (Set α) where
  union p q := fun a ↦ p a ∨ q a

instance : Inter (Set α) where
  inter p q := fun a ↦ p a ∧ q a

instance : SDiff (Set α) where
  sdiff p q := fun a ↦ p a ∧ ¬q a

end Set

/-- Binary relation. -/
abbrev Rel (α : Type u) (β : Type v) := α → β → Prop

namespace Rel

variable {α : Type u} {β : Type v} {γ : Type w}

/--
The empty relation.
-/
def Empty : α → β → Prop :=
  fun _ _ ↦ False

instance : EmptyCollection (Rel α β) := ⟨Empty⟩

/--
The full relation.
-/
def Full : α → β → Prop :=
  fun _ _ ↦ True

instance : HasSubset (Rel α β) where
  Subset r₁ r₂ := ∀ ⦃a : α⦄ ⦃b : β⦄ , r₁ a b → r₂ a b

/--
Composition of relations (sequencing).
-/
def Seq (r₁ : Rel α β) (r₂ : Rel β γ) : Rel α γ :=
  fun a c ↦ ∃ b, r₁ a b ∧ r₂ b c

/--
A state in which `P` holds is always reachable via `step` from
a given initial state `a`.
-/
inductive Eventually (step : Rel α α) (P : Set α) :
    α → Prop where
  /-- `P` holds in the initial state. -/
  | base ⦃a : α⦄ (ha : P a) : step.Eventually P a
  /-- `P` holds on along every possible path from the initial state. -/
  | step ⦃a : α⦄ (hs : ∃ a', step a a') (hss : step a ⊆ step.Eventually P) :
      step.Eventually P a

/--
Traditional Hoare triple.
-/
def Hoare (step : Rel α α) (pre post : Set α) : Prop :=
  pre ⊆ (step.Eventually post)

/--
Hoare triple with an explicit frame condition.
-/
def Ensures (step : Rel α α) (pre post : Set α)
    (frame : Rel α α) : Prop :=
  ∀ ⦃a : α⦄, pre a → step.Eventually (fun a' ↦ post a' ∧ frame a a') a

end Rel

#check HasSubset

@[inherit_doc] scoped infixr:64 " ,, " => Rel.Seq

end Bignum
