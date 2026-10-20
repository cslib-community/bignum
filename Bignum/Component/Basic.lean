/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

@[expose] public section

/-! # Basic components -/

namespace Bignum

universe u₁ u₂ u₃ u₄

/--
Component of type `β` in a larger state space `a`.
-/
structure Component (α : Type u₁) (β : Type u₂) where
  /-- Reader function. -/
  read : α → β
  /-- Writer function. -/
  write : β → α → α

namespace Component

/--
Type class stating that writing to then reading from `cp`
yields the written value.
-/
class ReadOverWrite
    {α : Type u₁} {β : Type u₂} (cp : Component α β) : Prop where
  /-- Reading after writing `b` to `a` yields `b`. -/
  read_over_write : ∀ b a, cp.read (cp.write b a) = b

/--
Type class stating that writing then reading from `cp`
yields a function of the written value.
-/
class WeakReadOverWrite
    {α : Type u₁} {β : Type u₂} (cp : Component α β) : Prop where
  /-- Reading after writing `b` to `a` yields `f b` for some `f`. -/
  weak_read_over_write : ∃ (f : β → β), ∀ b a, cp.read (cp.write b a) = f b

/--
Type class stating that reading then writing the value just
read to `cp` cancels the write.
-/
class WriteOverRead
    {α : Type u₁} {β : Type u₂} (cp : Component α β) : Prop where
  /-- Writing the current of the component value to `a` yields `a`. -/
  write_over_read : ∀ a, cp.write (cp.read a) a = a

/--
Type class stating that writing to `cp` twice cancels the first write.
-/
class WriteOverWrite
    {α : Type u₁} {β : Type u₂} (cp : Component α β) : Prop where
  /-- Writing `b₂` after writing `b₁` to `a` is
      the same as to writing `b₂` to `a`. -/
  write_over_write : ∀ b₁ b₂ a, cp.write b₂ (cp.write b₁ a) = cp.write b₂ a

/--
Type class stating that `cp` is valid, i.e., satisfies the `ReadOverWrite`
and `WriteOverWrite`.
-/
class abbrev Valid
    {α : Type u₁} {β : Type u₂} (cp : Component α β) : Prop :=
  ReadOverWrite cp, WriteOverWrite cp

/--
Type class stating that `cp` is weakly valid, i.e., satisfies
`WeakReadOverWrite` and `WriteOverWrite`.
-/
class abbrev WeaklyValid
    {α : Type u₁} {β : Type u₂} (cp : Component α β) : Prop :=
  WeakReadOverWrite cp, WriteOverWrite cp

/--
Type class stating that `cp` is strongly valid, i.e., satisfies
`ReadOverWrite`, `WriteOverWrite`, and `WriteOverRead`.
-/
class abbrev StronglyValid
    {α : Type u₁} {β : Type u₂} (cp : Component α β) : Prop :=
  Valid cp, WriteOverRead cp

/--
Composition of components.
-/
def compose {α : Type u₁} {β : Type u₂} {γ : Type u₃}
    (cp₁ : Component α β) (cp₂ : Component β γ) : Component α γ :=
  ⟨cp₂.read ∘ cp₁.read, fun c a ↦ cp₁.write (cp₂.write c (cp₁.read a)) a⟩

@[inherit_doc] infixr:90 " :> " => Component.compose

/--
"Identity" for components.
-/
def entirety {α : Type u₁} : Component α α :=
  ⟨id, fun x _ ↦ x⟩

/--
Pseudo-component for reading a value (write is no-op).
-/
def rvalue {α : Type u₁} {β : Type u₂} (b : β) : Component α β :=
  ⟨fun _ ↦ b, fun _ a ↦ a⟩

/--
Component for a function with a BEq domain.
-/
def element {α : Type u₁} [BEq α] {β : Type u₂} (a : α)
    : Component (α → β) β :=
  ⟨fun f ↦ f a, fun b f a' ↦ if a' == a then b else f a'⟩

/--
Component for applying a pair of functions (f,g) to a component.
-/
def through {α : Type u₁} {β : Type u₂} (f : α → β) (g : β → α)
    : Component α β :=
  ⟨f, fun b _ ↦ g b⟩

end Component
end Bignum
