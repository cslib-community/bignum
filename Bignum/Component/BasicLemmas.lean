/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Bignum.Component.Basic

@[expose] public section

/-! # Lemmas about the basic components -/

namespace Bignum.Component

universe u₁ u₂ u₃ u₄
variable {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄}

instance (cp : Component α β) [cp.ReadOverWrite] :
    cp.WeakReadOverWrite := by
  constructor; exists id; apply ReadOverWrite.read_over_write

instance (cp : Component α β) [cp.Valid] : cp.WeaklyValid := by
  constructor

instance (cp : Component α β) [cp.StronglyValid] :
    cp.ExtensionallyValid := by
  constructor

/-! ## compose -/

theorem compose_assoc
    (cp₁ : Component α β) (cp₂ : Component β γ) (cp₃ : Component γ δ) :
    cp₁ :> (cp₂ :> cp₃) = (cp₁ :> cp₂) :> cp₃ := by
  rfl

theorem read_compose (cp₁ : Component α β) (cp₂ : Component β γ) (a : α) :
    (cp₁ :> cp₂).read a = cp₂.read (cp₁.read a) := by
  rfl

theorem write_compose
    (cp₁ : Component α β) (cp₂ : Component β γ) (a : α) (c : γ) :
    (cp₁ :> cp₂).write c a = cp₁.write (cp₂.write c (cp₁.read a)) a := by
  rfl

theorem read_write_compose
    (cp₁ : Component α β) (cp₂ : Component β γ)
    (h₁ : ∀ b a, cp₁.read (cp₁.write b a) = b)
    (h₂ : ∀ c b, cp₂.read (cp₂.write c b) = c)
    (c : γ) (a : α) :
    (cp₁ :> cp₂).read ((cp₁ :> cp₂).write c a) = c := by
  rw [read_compose, write_compose, h₁, h₂]

instance (cp₁ : Component α β) (cp₂ : Component β γ)
    [cp₁.ReadOverWrite] [cp₂.ReadOverWrite] :
    ReadOverWrite (cp₁ :> cp₂) where
  read_over_write := by
    intros; apply read_write_compose
    · apply ReadOverWrite.read_over_write
    · apply ReadOverWrite.read_over_write

instance (cp₁ : Component α β) (cp₂ : Component β γ)
    [cp₁.WriteOverRead] [cp₂.WriteOverRead] :
    (cp₁ :> cp₂).WriteOverRead where
  write_over_read := by
    intros; rw [write_compose, read_compose,
      WriteOverRead.write_over_read, WriteOverRead.write_over_read]

instance (cp₁ : Component α β) (cp₂ : Component β γ)
    [cp₁.ReadOverWrite] [cp₁.WriteOverWrite] [cp₂.WriteOverWrite] :
    (cp₁ :> cp₂).WriteOverWrite := by
    constructor; intros; simp [write_compose, ReadOverWrite.read_over_write,
      WriteOverWrite.write_over_write]

instance (cp₁ : Component α β) (cp₂ : Component β γ)
    [cp₁.Valid] [cp₂.Valid] :
    (cp₁ :> cp₂).Valid := by
  constructor

instance (cp₁ : Component α β) (cp₂ : Component β γ)
    [cp₁.StronglyValid] [cp₂.StronglyValid] :
    (cp₁ :> cp₂).StronglyValid := by
  constructor

/-! ## entirety -/

theorem read_entirety (a : α) : entirety.read a = a := by
  rfl

theorem write_entirety (a a' : α) : entirety.write a a' = a := by
  rfl

theorem read_write_entirety (a a' : α) :
    entirety.read (entirety.write a a') = a := by
  rfl

instance : ReadOverWrite (@entirety α) where
  read_over_write := read_write_entirety

instance : WeakReadOverWrite (@entirety α) where
  weak_read_over_write := by exists id; apply read_write_entirety

instance : WriteOverRead (@entirety α) where
  write_over_read := by simp [write_entirety, read_entirety]

instance : WriteOverWrite (@entirety α) where
  write_over_write := by simp [write_entirety]

theorem compose_entirety_right (cp : Component α β) :
    cp :> entirety = cp := by
  rfl

theorem compose_entirety_left (cp : Component α β) :
    entirety :> cp = cp := by
  rfl

end Bignum.Component
