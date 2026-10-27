/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Bignum.Relation.Basic

@[expose] public section

/-! # Lemmas about relations and Hoare-type rules -/

namespace Bignum.Relation

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

/-! ## Subsumed (⊑) -/

theorem Subsumed_Seq (r₁ r₂ : α → β → Prop) (t₁ t₂ : β → γ → Prop)
    (h₁ : r₁ ⊑ r₂) (h₂ : t₁ ⊑ t₂) : r₁ ,, t₁ ⊑ r₂ ,, t₂ := by
  unfold Subsumed Seq at *
  intro _ _ ⟨b', hr₁, ht₁⟩; exact ⟨b', h₁ hr₁, h₂ ht₁⟩

theorem Subsumed_for_Seq (r s t : α → α → Prop)
    (hr : r ⊑ t) (hs : s ⊑ t) (ht : t ,, t = t) : r ,, s ⊑ t := by
  unfold Subsumed Seq at *
  intro a b ⟨c, hac, hcb⟩; rw [← ht]; exact ⟨c, hr hac, hs hcb⟩

theorem Subsumed_Eq_Seq (r r' : α → α → Prop) (h₁ : Eq ⊑ r) (h₂ : Eq ⊑ r') :
    Eq ⊑ r ,, r' := by
  unfold Subsumed Seq at *
  intro a a' _; subst a'
  exact ⟨a, h₁ (@Eq.refl _ a), h₂ (@Eq.refl _ a)⟩

theorem Subsumed_refl (r : α → β → Prop) : r ⊑ r := by
  unfold Subsumed; exact (fun h ↦ h)

theorem Subsumed_Seq_left (r r' : α → β → Prop) (rb : β → β → Prop)
    (h₁ : r ⊑ r') (h₂ : Eq ⊑ rb) :
    r ⊑ r' ,, rb := by
  unfold Subsumed Seq at *
  intro _ b hab; exact ⟨b, h₁ hab, h₂ (@Eq.refl _ b)⟩

theorem Subsumed_Seq_right (r r' : α → β → Prop) (ra : α → α → Prop)
    (h₁ : Eq ⊑ ra) (h₂ : r ⊑ r') :
    r ⊑ ra ,, r' := by
  unfold Subsumed Seq at *
  intro a _ hab; exact ⟨a, h₁ (@Eq.refl _ a), h₂ hab⟩

theorem Subsumed_trivial (r : α → α → Prop) : r ⊑ (fun _ _ ↦ True) := by
  unfold Subsumed; intros; exact True.intro

/-! ## Eventually -/

theorem Eventually_mono (step : Relation α α) (P Q : α → Prop)
    (hPQ : ∀ a, P a → Q a) (a : α) (hE : step.Eventually P a) :
    step.Eventually Q a := by
  induction hE with
  | base => apply Eventually.base; apply hPQ; assumption
  | step hs _ ih =>
    apply Eventually.step hs ih

theorem Eventually_imp_Eventualy (step : Relation α α) (P Q : α → Prop) :
    (∀ a, step.Eventually P a → step.Eventually Q a) ↔
    (∀ a, P a → step.Eventually Q a) := by
  constructor
  · intro h _ hP; apply h; apply Eventually.base hP
  · intro h a hE; induction hE with
    | base hP => apply h _ hP
    | step hs _ ih => apply Eventually.step hs ih

/-! ## Ensures -/

theorem Ensures_pre_post_gen (step : Relation α α) (P P' Q Q' : α → Prop)
    (C C' : Relation α α) (hP : ∀ x, P' x → P x) (hQ : ∀ x, Q x → Q' x)
    (hC : C ⊑ C') (h : step.Ensures P Q C) :
    step.Ensures P' Q' C' := by
  unfold Ensures at *; intro a ha
  apply Eventually_mono (hE := h _ (hP _ ha))
  intro a' ⟨hl, hr⟩; constructor
  · apply hQ _ hl
  · apply hC hr

theorem Ensures_pre_post (step : Relation α α) (P P' Q Q' : α → Prop)
    (C : Relation α α) (hP : ∀ x, P' x → P x) (hQ : ∀ x, Q x → Q' x)
    (h : step.Ensures P Q C) :
    step.Ensures P' Q' C := by
  apply Ensures_pre_post_gen
    (hP := hP) (hQ := hQ) (hC := Subsumed_refl _) (h := h)

theorem Ensures_pre_gen (step : Relation α α) (P P' Q : α → Prop)
    (C C' : Relation α α) (hP : ∀ x, P' x → P x) (hC : C ⊑ C')
    (h : step.Ensures P Q C) :
    step.Ensures P' Q C' := by
  apply Ensures_pre_post_gen
    (hP := hP) (hQ := fun _ ↦ id) (hC := hC) (h := h)

theorem Ensures_pre (step : Relation α α) (P P' Q : α → Prop)
    (C : Relation α α) (hP : ∀ x, P' x → P x) (h : step.Ensures P Q C) :
    step.Ensures P' Q C := by
  apply Ensures_pre_gen (hP := hP) (hC := Subsumed_refl _) (h := h)

theorem Ensures_post_gen (step : Relation α α) (P Q Q' : α → Prop)
    (C C' : Relation α α) (hQ : ∀ x, Q x → Q' x) (hC : C ⊑ C')
    (h : step.Ensures P Q C) :
    step.Ensures P Q' C' := by
  apply Ensures_pre_post_gen
    (hP := fun _ ↦ id) (hQ := hQ) (hC := hC) (h := h)

theorem Ensures_post (step : Relation α α) (P Q Q' : α → Prop)
    (C : Relation α α) (hQ : ∀ x, Q x → Q' x) (h : step.Ensures P Q C) :
    step.Ensures P Q' C := by
  apply Ensures_post_gen (hQ := hQ) (hC := Subsumed_refl _) (h := h)

end Bignum.Relation
