/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Bignum.Component.BasicLemmas
public import Bignum.Component.Extra

@[expose] public section

/-! # Lemmas about the extra components -/

namespace Bignum.Component

universe u₁ u₂ u₃ u₄
variable {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄}

/-! ## rvalue -/

theorem read_rvalue (a : α) (b : β) :
    (rvalue b).read a = b := by
  rfl

theorem write_rvalue (a : α) (b b' : β) :
    (rvalue b).write b' a = a := by
  rfl

theorem compose_rvalue_left (b : β) (cp : Component β γ) :
    (@rvalue α _ b) :> cp = rvalue (cp.read b) := by
  rw [compose, rvalue]; funext; rfl

theorem compose_rvalue_right
    (cp : Component α β) [h : cp.ExtensionallyValid] (c : γ) :
    cp :> (rvalue c) = rvalue c := by
  simp [compose, rvalue]; constructor <;>
  funext; rfl; apply h.write_over_read

instance (cp : Component α β) (c : γ) : cp.Orthogonal (rvalue c) := by
  constructor <;> intros
  · simp [write_rvalue]
  · simp [read_rvalue]
  · rw [write_rvalue]

instance (c : γ) (cp : Component α β) : (rvalue c).Orthogonal cp := by
  constructor <;> intros
  · simp [write_rvalue]
  · rw [write_rvalue]
  · simp [read_rvalue]

instance (cp₁ : Component α β) (b : β) (cp₂ : Component β γ) :
    cp₁.Orthogonal (rvalue b :> cp₂) := by
  constructor <;> simp [compose_rvalue_left]
  · simp [write_rvalue]
  · simp [read_rvalue]
  · simp [write_rvalue]

instance (b : β) (cp₂ : Component β γ) (cp₁ : Component α β) :
    (rvalue b :> cp₂).Orthogonal cp₁ := by
  constructor <;> simp [compose_rvalue_left]
  · simp [write_rvalue]
  · simp [write_rvalue]
  · simp [read_rvalue]

end Bignum.Component
