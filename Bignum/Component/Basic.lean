/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Guilherme Lima
-/
module

@[expose] public section

/-! # Basic components -/

-- Ported from HOL-Light (Library/components.ml).

set_option autoImplicit false

namespace Bignum

universe u₁ u₂ u₃ u₄

/--
Component of type `b` in a composite of type `a`.
-/
structure Component (α : Type u₁) (β : Type u₂) where
  /-- Reader function. -/
  read : α → β
  /-- Writer function. -/
  write : β → α → α

namespace Component

variable {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄}

/--
Composition of components.
-/
def compose (cp₁ : Component α β) (cp₂ : Component β γ) : Component α γ :=
  ⟨cp₂.read ∘ cp₁.read, λ c a ↦ cp₁.write (cp₂.write c (cp₁.read a)) a⟩

infixr:90 ":>" => compose

theorem compose_assoc
    (cp₁ : Component α β) (cp₂ : Component β γ) (cp₃ : Component γ δ) :
    cp₁ :> (cp₂ :> cp₃) = (cp₁ :> cp₂) :> cp₃ := by
  rfl

theorem compose_read (cp₁ : Component α β) (cp₂ : Component β γ) (a : α) :
    (cp₁ :> cp₂).read a = cp₂.read (cp₁.read a) := by
  rfl

theorem compose_write
    (cp₁ : Component α β) (cp₂ : Component β γ) (a : α) (c : γ) :
    (cp₁ :> cp₂).write c a = cp₁.write (cp₂.write c (cp₁.read a)) a := by
  rfl

theorem read_write_compose
    (cp₁ : Component α β) (cp₂ : Component β γ)
    (h₁ : ∀ b a, cp₁.read (cp₁.write b a) = b)
    (h₂ : ∀ c b, cp₂.read (cp₂.write c b) = c)
    (c : γ) (a : α) :
    (cp₁ :> cp₂).read ((cp₁ :> cp₂).write c a) = c := by
  rw [compose_read, compose_write, h₁, h₂]

/--
"Identity" for components.
-/
def entirety : Component α α :=
  ⟨id, λ x _ ↦ x⟩

theorem entirety_read (a : α) : entirety.read a = a := by
  rfl

theorem entirety_write (a a' : α) : entirety.write a' a = a' := by
  rfl

theorem entirety_read_write (a a' : α) :
    entirety.read (entirety.write a' a) = a' := by
  rfl

theorem compose_entirety (cp : Component α β) :
    cp :> entirety = cp := by
  rfl

theorem entirety_compose (cp : Component α β) :
    entirety :> cp = cp := by
  rfl

/--
Pseudo-component for reading a value (read-only).
-/
def rvalue (b : β) : Component α β :=
  ⟨λ _ ↦ b, λ _ a ↦ a⟩

/--
Component corresponding to a function with a BEq domain.
-/
def element [BEq α] (a : α) : Component (α → β) β :=
  ⟨λ f ↦ f a, λ b f a' ↦ if a' == a then b else f a'⟩

/--
Component that applies a pair of functions (f,g) to a component.
-/
def through (f : α → β) (g : β → α) : Component α β :=
  ⟨f, λ b _ ↦ g b⟩

end Component
