/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Bignum.Component.Basic

@[expose] public section

/-! # Lemmas about components -/

namespace Bignum.Component

universe u₁ u₂ u₃ u₄
variable {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄}

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

theorem ReadOverWrite.compose (cp₁ : Component α β) (cp₂ : Component β γ)
    [hr₁ : cp₁.ReadOverWrite] [hr₂ : cp₂.ReadOverWrite] :
    (cp₁ :> cp₂).ReadOverWrite := by
  constructor; intros c a
  apply read_write_compose _ _ hr₁.read_over_write hr₂.read_over_write

theorem WriteOverRead.compose (cp₁ : Component α β) (cp₂ : Component β γ)
    [hw₁ : cp₁.WriteOverRead] [hw₂ : cp₂.WriteOverRead] :
    (cp₁ :> cp₂).WriteOverRead := by
  constructor; intro a; rw [write_compose, read_compose,
    hw₂.write_over_read, hw₁.write_over_read]

theorem WriteOverWrite.compose (cp₁ : Component α β) (cp₂ : Component β γ)
    [hr₁ : cp₁.ReadOverWrite] [hw₁ : cp₁.WriteOverWrite]
    [hw₂ : cp₂.WriteOverWrite] :
    (cp₁ :> cp₂).WriteOverWrite := by
  constructor; intros c c' a; simp [write_compose,
    hr₁.read_over_write, hw₁.write_over_write, hw₂.write_over_write]

theorem Valid.compose (cp₁ : Component α β) (cp₂ : Component β γ)
    [hv₁ : cp₁.Valid] [hv₂ : cp₂.Valid] :
    (cp₁ :> cp₂).Valid := by
  refine @Valid.mk _ _ (cp₁ :> cp₂) ?r ?w
  · apply ReadOverWrite.compose
  · apply WriteOverWrite.compose

theorem StronglyValid.compose (cp₁ : Component α β) (cp₂ : Component β γ)
    [hs₁ : cp₁.StronglyValid] [hs₂ : cp₂.StronglyValid] :
    (cp₁ :> cp₂).StronglyValid := by
  apply @StronglyValid.mk _ _ (cp₁ :> cp₂) ?v ?w
  · apply Valid.compose
  · apply WriteOverRead.compose

/-! ## entirety -/

theorem read_entirety (a : α) : entirety.read a = a := by
  rfl

theorem write_entirety (a a' : α) : entirety.write a a' = a := by
  rfl

theorem read_write_entirety (a a' : α) :
    entirety.read (entirety.write a a') = a := by
  rfl

instance {α : Type u₁} : Valid (@entirety α) where
  read_over_write := read_write_entirety
  write_over_write := by simp [write_entirety]

instance {α : Type u₁} : StronglyValid (@entirety α) where
  write_over_read := by simp [write_entirety, read_entirety]

theorem compose_entirety_right (cp : Component α β) :
    cp :> entirety = cp := by
  rfl

theorem compose_entirety_left (cp : Component α β) :
    entirety :> cp = cp := by
  rfl

end Bignum.Component
