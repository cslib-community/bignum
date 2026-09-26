/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Guilherme Lima
-/
module

public import Bignum.Relational.Basic

@[expose] public section

/-! # Lemmas about relations and rules -/

set_option autoImplicit false

namespace Bignum.Relational

universe u₁ u₂ u₃ u₄
variable {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄}

/-! ## seq (,,) -/

theorem seq_assoc
    (r₁ : α → β → Prop) (r₂ : β → γ → Prop) (r₃ : γ → δ → Prop) :
    r₁ ,, r₂ ,, r₃ = (r₁ ,, r₂) ,, r₃ := by
  unfold seq; ext a d; constructor
  · intro ⟨b, hab, c, hbc, hcd⟩; exact ⟨c, ⟨b, hab, hbc⟩, hcd⟩
  · intro ⟨c, ⟨b, hab, hbc⟩, hcd⟩; exact ⟨b, hab, c, hbc, hcd⟩

theorem seq_id_left (r : α → β → Prop) : Eq ,, r = r := by
  unfold seq; ext a b; constructor
  · intro ⟨_, h, _⟩; rw [h]; assumption
  · intro; exists a

theorem seq_id_right (r : α → β → Prop) : r ,, Eq = r := by
  unfold seq; ext a b; constructor
  · intro ⟨_, _, h⟩; rw [← h]; assumption
  · intro; exists b

theorem seq_trivial [Inhabited β] :
    (λ (_ : α) _ ↦ True) ,, (λ (_ : β) (_ : γ) ↦ True) = (λ _ _ ↦ True) := by
  unfold seq; simp

theorem seq_preserves_component (cp : Component α β)
    (r : α → α → Prop) (t : α → α → Prop) (a a' : α)
    (hr : ∀ x y, r x y → cp.read x = cp.read y)
    (ht : ∀ x y, t x y → cp.read x = cp.read y) :
    (r ,, t) a a' → cp.read a' = cp.read a := by
  unfold seq; intro ⟨x, hax, hxa'⟩; rw [hr _ _ hax, ht _ _ hxa']

/-! ## subsumed (⊑) -/

theorem subsumed_seq (r₁ r₂ : α → β → Prop) (t₁ t₂ : β → γ → Prop)
    (h₁ : r₁ ⊑ r₂) (h₂ : t₁ ⊑ t₂) : r₁ ,, t₁ ⊑ r₂ ,, t₂ := by
  unfold subsumed seq at *
  intro _ _ ⟨b', hr₁, ht₁⟩; exact ⟨b', h₁ _ _ hr₁, h₂ _ _ ht₁⟩

theorem subsumed_for_seq (r s t : α → α → Prop)
    (hr : r ⊑ t) (hs : s ⊑ t) (ht : t ,, t = t) : r ,, s ⊑ t := by
  unfold subsumed seq at *
  intro a b ⟨c, hac, hcb⟩; rw [← ht]; exact ⟨c, hr _ _ hac, hs _ _ hcb⟩

theorem subsumed_id_seq (r r' : α → α → Prop) (h₁ : Eq ⊑ r) (h₂ : Eq ⊑ r') :
    Eq ⊑ r ,, r' := by
  unfold subsumed seq at *
  intro a a' _; subst a'
  exact ⟨a, h₁ _ _ (@Eq.refl _ a), h₂ _ _ (@Eq.refl _ a)⟩

theorem subsumed_refl (r : α → β → Prop) : r ⊑ r := by
  unfold subsumed; exact (λ _ _ h ↦ h)

theorem subsumed_seq_left (r r' : α → β → Prop) (rb : β → β → Prop)
    (h₁ : r ⊑ r') (h₂ : Eq ⊑ rb) :
    r ⊑ r' ,, rb := by
  unfold subsumed seq at *
  intro _ b hab; exact ⟨b, h₁ _ _ hab, h₂ _ _ (@Eq.refl _ b)⟩

theorem subsumed_seq_right (r r' : α → β → Prop) (ra : α → α → Prop)
    (h₁ : Eq ⊑ ra) (h₂ : r ⊑ r') :
    r ⊑ ra ,, r' := by
  unfold subsumed seq at *
  intro a _ hab; exact ⟨a, h₁ _ _ (@Eq.refl _ a), h₂ _ _ hab⟩

theorem subsumed_triival (r : α → α → Prop) : r ⊑ (λ _ _ ↦ True) := by
  unfold subsumed; intros; exact True.intro

/-! ## assign (≔) -/

theorem assign_seq (cp : Component α β) (b : β) (r : α → β → Prop) (a : α) :
    ((cp ≔ b) ,, r) a = r (cp.write b a) := by
  unfold seq assign; simp

-- theorem assign_zerotop_8 (cp : Component α (BitVec 16)) (bv : BitVec 8) :
--     ((cp :> .zerotop_8) ≔ bv) = (cp ≔ bv.zeroExtend 16) := by
--   unfold assign Component.compose; simp
--   sorry


end Bignum.Relational
