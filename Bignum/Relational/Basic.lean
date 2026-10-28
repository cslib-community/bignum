/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

@[expose] public section

/-! # Relational model of programs and Hoare-rules -/

namespace Bignum

universe u v

/-- Unary predicate. -/
abbrev Predicate (α : Type u) := α → Prop

namespace Predicate

variable {α : Type u}

/--
The empty predicate.
-/
def Empty : α → Prop :=
  fun _ ↦ False

/--
The full predicate.
-/
def Full : α → Prop :=
  fun _ ↦ True

/--
Subsumption of predicates.
-/
def Subsumed (p p' : Predicate α) : Prop :=
  ∀ {a}, p a → p' a


end Predicate

/-- Binary relation. -/
abbrev Relation (α : Type u) (β : Type v) := α → β → Prop

namespace Relation

universe u₁ u₂ u₃ u₄

variable {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄}

/--
The empty relation.
-/
def Empty : α → β → Prop :=
  fun _ _ ↦ False

/--
The full relation.
-/
def Full : α → β → Prop :=
  fun _ _ ↦ True

/--
Subsumption of relations.
-/
def Subsumed (r r' : Relation α β) : Prop :=
  ∀ {a} {b}, r a b → r' a b

/--
Composition of relations (sequencing).
-/
def Seq (r₁ : Relation α β) (r₂ : Relation β γ) : Relation α γ :=
  fun a c ↦ ∃ b, r₁ a b ∧ r₂ b c

/--
`(Eventually step P a)` iff `P` is always reachable from state `a` via `step`.
-/
inductive Eventually (step : Relation α α) (P : Predicate α) :
    α → Prop where
  /-- `P` holds in the initial state. -/
  | base {a} (ha : P a) : step.Eventually P a
  /-- `P` holds on along every possible path from the initial state. -/
  | step {a} (hs : ∃ a', step a a')
      (hss : ∀ a', step a a' → step.Eventually P a') :
      step.Eventually P a

/--
Traditional Hoare triple.
-/
def Hoare (step : Relation α α) (pre post : Predicate α) : Prop :=
  pre.Subsumed (step.Eventually post)

/--
Hoare triple with an explicit frame condition.
-/
def Ensures (step : Relation α α) (pre post : Predicate α)
    (frame : Relation α α) : Prop :=
  forall a, pre a → step.Eventually (fun a' ↦ post a' ∧ frame a a') a

end Relation

@[inherit_doc] scoped infixr:50 " ⊑ " => Predicate.Subsumed
@[inherit_doc] scoped infixr:50 " ⊑ " => Relation.Subsumed
@[inherit_doc] scoped infixr:64 " ,, " => Relation.Seq

end Bignum
