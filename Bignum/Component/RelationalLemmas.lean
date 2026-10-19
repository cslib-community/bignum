/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Bignum.Component.Extra
public import Bignum.Component.Relational

@[expose] public section

/-! # Lemmas about relations and rules -/

namespace Bignum.Component

universe u₁ u₂ u₃ u₄
variable {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄}

/-! ## Seq (,,) -/

theorem Seq_assoc
    (r₁ : α → β → Prop) (r₂ : β → γ → Prop) (r₃ : γ → δ → Prop) :
    r₁ ,, r₂ ,, r₃ = (r₁ ,, r₂) ,, r₃ := by
  unfold Seq; ext a d; constructor
  · intro ⟨b, hab, c, hbc, hcd⟩; exact ⟨c, ⟨b, hab, hbc⟩, hcd⟩
  · intro ⟨c, ⟨b, hab, hbc⟩, hcd⟩; exact ⟨b, hab, c, hbc, hcd⟩

theorem Seq_Eq_left (r : α → β → Prop) : Eq ,, r = r := by
  unfold Seq; ext a b; constructor
  · intro ⟨_, h, _⟩; rw [h]; assumption
  · intro; exists a

theorem Seq_Eq_right (r : α → β → Prop) : r ,, Eq = r := by
  unfold Seq; ext a b; constructor
  · intro ⟨_, _, h⟩; rw [← h]; assumption
  · intro; exists b

theorem Seq_trivial [Inhabited β] :
    (fun (_ : α) _ ↦ True) ,, (fun (_ : β) (_ : γ) ↦ True) =
    (fun _ _ ↦ True) := by
  unfold Seq; simp

theorem Seq_preserves_component (cp : Component α β)
    (r : α → α → Prop) (t : α → α → Prop) (a a' : α)
    (hr : ∀ x y, r x y → cp.read x = cp.read y)
    (ht : ∀ x y, t x y → cp.read x = cp.read y) :
    (r ,, t) a a' → cp.read a' = cp.read a := by
  unfold Seq; intro ⟨x, hax, hxa'⟩; rw [hr _ _ hax, ht _ _ hxa']

/-! ## Subsumed (⊑) -/

theorem Subsumed_Seq (r₁ r₂ : α → β → Prop) (t₁ t₂ : β → γ → Prop)
    (h₁ : r₁ ⊑ r₂) (h₂ : t₁ ⊑ t₂) : r₁ ,, t₁ ⊑ r₂ ,, t₂ := by
  unfold Subsumed Seq at *
  intro _ _ ⟨b', hr₁, ht₁⟩; exact ⟨b', h₁ _ _ hr₁, h₂ _ _ ht₁⟩

theorem Subsumed_for_Seq (r s t : α → α → Prop)
    (hr : r ⊑ t) (hs : s ⊑ t) (ht : t ,, t = t) : r ,, s ⊑ t := by
  unfold Subsumed Seq at *
  intro a b ⟨c, hac, hcb⟩; rw [← ht]; exact ⟨c, hr _ _ hac, hs _ _ hcb⟩

theorem Subsumed_Eq_Seq (r r' : α → α → Prop) (h₁ : Eq ⊑ r) (h₂ : Eq ⊑ r') :
    Eq ⊑ r ,, r' := by
  unfold Subsumed Seq at *
  intro a a' _; subst a'
  exact ⟨a, h₁ _ _ (@Eq.refl _ a), h₂ _ _ (@Eq.refl _ a)⟩

theorem Subsumed_refl (r : α → β → Prop) : r ⊑ r := by
  unfold Subsumed; exact (fun _ _ h ↦ h)

theorem Subsumed_Seq_left (r r' : α → β → Prop) (rb : β → β → Prop)
    (h₁ : r ⊑ r') (h₂ : Eq ⊑ rb) :
    r ⊑ r' ,, rb := by
  unfold Subsumed Seq at *
  intro _ b hab; exact ⟨b, h₁ _ _ hab, h₂ _ _ (@Eq.refl _ b)⟩

theorem Subsumed_Seq_right (r r' : α → β → Prop) (ra : α → α → Prop)
    (h₁ : Eq ⊑ ra) (h₂ : r ⊑ r') :
    r ⊑ ra ,, r' := by
  unfold Subsumed Seq at *
  intro a _ hab; exact ⟨a, h₁ _ _ (@Eq.refl _ a), h₂ _ _ hab⟩

theorem Subsumed_trivial (r : α → α → Prop) : r ⊑ (fun _ _ ↦ True) := by
  unfold Subsumed; intros; exact True.intro

/-! ## Assign (≔) -/

theorem Assign_Seq (cp : Component α β) (b : β) (r : α → β → Prop) (a : α) :
    ((cp ≔ b) ,, r) a = r (cp.write b a) := by
  unfold Seq Assign; simp

theorem Assign_zerotop8 (cp : Component α (BitVec 16)) (bv : BitVec 8) :
    ((cp :> .zerotop8) ≔ bv) = (cp ≔ bv.zeroExtend 16) := by
  unfold Assign; simp [Component.zerotop8]

theorem Assign_zerotop16 (cp : Component α (BitVec 32)) (bv : BitVec 16) :
    ((cp :> .zerotop16) ≔ bv) = (cp ≔ bv.zeroExtend 32) := by
  unfold Assign; simp [Component.zerotop16]

theorem Assign_zerotop32 (cp : Component α (BitVec 64)) (bv : BitVec 32) :
    ((cp :> .zerotop32) ≔ bv) = (cp ≔ bv.zeroExtend 64) := by
  unfold Assign; simp [Component.zerotop32]

theorem Assign_zerotop64 (cp : Component α (BitVec 128)) (bv : BitVec 64) :
    ((cp :> .zerotop64) ≔ bv) = (cp ≔ bv.zeroExtend 128) := by
  unfold Assign; simp [Component.zerotop64]

theorem Assign_zerotop128 (cp : Component α (BitVec 256)) (bv : BitVec 128) :
    ((cp :> .zerotop128) ≔ bv) = (cp ≔ bv.zeroExtend 256) := by
  unfold Assign; simp [Component.zerotop128]

theorem Assign_zerotop256 (cp : Component α (BitVec 512)) (bv : BitVec 256) :
    ((cp :> .zerotop256) ≔ bv) = (cp ≔ bv.zeroExtend 512) := by
  unfold Assign; simp [Component.zerotop256]

/-! ## Assigns -/

end Bignum.Component
