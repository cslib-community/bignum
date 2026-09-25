/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Guilherme Lima
-/
module

@[expose] public section

set_option autoImplicit false

namespace Bignum.Relational

universe u v w w'

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type w'}

/--
Composition of relations (i.e., sequencing).
-/
def seq (r₁ : α → β → Prop) (r₂ : β → γ → Prop) : α → γ → Prop :=
  λ a c ↦ ∃ b, r₁ a b ∧ r₂ b c

infixr:62 " ,, " => seq

theorem seq_assoc
    (r₁ : α → β → Prop) (r₂ : β → γ → Prop) (r₃ : γ → δ → Prop) :
    r₁ ,, r₂ ,, r₃ = (r₁ ,, r₂) ,, r₃ := by
  unfold seq; ext a d; constructor
  · rintro ⟨b, hab, c, hbc, hcd⟩; exact ⟨c, ⟨b, hab, hbc⟩, hcd⟩
  · rintro ⟨c, ⟨b, hab, hbc⟩, hcd⟩; exact ⟨b, hab, c, hbc, hcd⟩

theorem seq_id_left (r : α → β → Prop) : Eq ,, r = r := by
  unfold seq; ext a b; constructor
  · rintro ⟨_, h, _⟩; rw [h]; assumption
  · intro; exists a

end Bignum.Relational
