/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Bignum.Relational.Basic

@[expose] public section

/-! # Lemmas about relations and Hoare-type rules -/

/-! ## Predicate -/

namespace Bignum.Predicate

universe u

variable {α : Type u}

theorem empty_subsumed (p : Predicate α) : .Empty ⊑ p := by
  unfold Subsumed Empty; intros; contradiction

theorem subsumed_full (p : Predicate α) : p ⊑ .Full := by
  unfold Subsumed; intros; exact True.intro

theorem subsumed_refl (p : Predicate α) : p ⊑ p := by
  unfold Subsumed; exact (fun h ↦ h)

instance : Std.Refl (@Subsumed α) where
  refl r := subsumed_refl r

theorem subsumed_antisymm (p₁ p₂ : Predicate α)
    (hl : p₁ ⊑ p₂) (hr : p₂ ⊑ p₁) : p₁ = p₂ := by
  funext; exact propext ⟨hl, hr⟩

instance : Std.Antisymm (@Subsumed α) where
  antisymm p₁ p₂ := subsumed_antisymm p₁ p₂

theorem subsumed_trans (p₁ p₂ p₃ : Predicate α) :
    p₁ ⊑ p₂ → p₂ ⊑ p₃ → p₁ ⊑ p₃ := by
  unfold Subsumed; intro ab cd _ _; apply cd; apply ab; assumption

end Bignum.Predicate

/-! ## Relation -/

namespace Bignum.Relation

universe u₁ u₂ u₃ u₄
variable {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄}

/-! ### Subsumed (⊑) -/

theorem empty_subsumed (r : Relation α β) : .Empty ⊑ r := by
  unfold Subsumed Empty; intros; contradiction

theorem subsumed_full (r : Relation α β) : r ⊑ .Full := by
  unfold Subsumed; intros; exact True.intro

theorem subsumed_refl (r : Relation α β) : r ⊑ r := by
  unfold Subsumed; exact (fun h ↦ h)

instance : Std.Refl (@Subsumed α β) where
  refl r := subsumed_refl r

theorem subsumed_antisymm (r₁ r₂ : Relation α β)
    (hl : r₁ ⊑ r₂) (hr : r₂ ⊑ r₁) : r₁ = r₂ := by
  funext; exact propext ⟨hl, hr⟩

instance : Std.Antisymm (@Subsumed α β) where
  antisymm r₁ r₂ := @subsumed_antisymm _ _ r₁ r₂

theorem subsumed_trans (r₁ r₂ r₃ : Relation α β) :
    r₁ ⊑ r₂ → r₂ ⊑ r₃ → r₁ ⊑ r₃ := by
  unfold Subsumed; intro ab cd _ _ _; apply cd; apply ab; assumption

/-! ### Seq (,,) -/

theorem seq_assoc
    (r₁ : Relation α β) (r₂ : Relation β γ) (r₃ : Relation γ δ) :
    r₁ ,, r₂ ,, r₃ = (r₁ ,, r₂) ,, r₃ := by
  unfold Seq; ext a d; constructor
  · intro ⟨b, hab, c, hbc, hcd⟩; exact ⟨c, ⟨b, hab, hbc⟩, hcd⟩
  · intro ⟨c, ⟨b, hab, hbc⟩, hcd⟩; exact ⟨b, hab, c, hbc, hcd⟩

theorem seq_eq_left (r : Relation α β) : Eq ,, r = r := by
  unfold Seq; ext a b; constructor
  · intro ⟨_, h, _⟩; rw [h]; assumption
  · intro; exists a

theorem seq_eq_right (r : Relation α β) : r ,, Eq = r := by
  unfold Seq; ext a b; constructor
  · intro ⟨_, _, h⟩; rw [← h]; assumption
  · intro; exists b

theorem seq_full_full [Inhabited β] : @.Full α β ,, @.Full β γ = .Full := by
  unfold Seq Full; simp

theorem subsumed_seq_seq (r₁ r₂ : Relation α β) (t₁ t₂ : Relation β γ)
    (h₁ : r₁ ⊑ r₂) (h₂ : t₁ ⊑ t₂) : r₁ ,, t₁ ⊑ r₂ ,, t₂ := by
  unfold Subsumed Seq at *
  intro _ _ ⟨b', hr₁, ht₁⟩; exact ⟨b', h₁ hr₁, h₂ ht₁⟩

theorem subsumed_seq_left (r s t : Relation α α)
    (hr : r ⊑ t) (hs : s ⊑ t) (ht : t ,, t = t) : r ,, s ⊑ t := by
  unfold Subsumed Seq at *
  intro a b ⟨c, hac, hcb⟩; rw [← ht]; exact ⟨c, hr hac, hs hcb⟩

theorem subsumed_eq_seq (r r' : Relation α α) (h₁ : Eq ⊑ r) (h₂ : Eq ⊑ r') :
    Eq ⊑ r ,, r' := by
  unfold Subsumed Seq at *
  intro a a' _; subst a'
  exact ⟨a, h₁ (@Eq.refl _ a), h₂ (@Eq.refl _ a)⟩

theorem subsumed_seq_eq_right (r r' : Relation α β) (rb : Relation β β)
    (h₁ : r ⊑ r') (h₂ : Eq ⊑ rb) :
    r ⊑ r' ,, rb := by
  unfold Subsumed Seq at *
  intro _ b hab; exact ⟨b, h₁ hab, h₂ (@Eq.refl _ b)⟩

theorem subsumed_seq_eq_left (r r' : Relation α β) (ra : Relation α α)
    (h₁ : Eq ⊑ ra) (h₂ : r ⊑ r') :
    r ⊑ ra ,, r' := by
  unfold Subsumed Seq at *
  intro a _ hab; exact ⟨a, h₁ (@Eq.refl _ a), h₂ hab⟩

/-! ### Eventually -/

variable {step : Relation α α}
variable {P P' Q Q' R J : Predicate α} {C C' : Relation α α}

theorem eventually_mono (hPQ : P ⊑ Q) :
    step.Eventually P ⊑ step.Eventually Q := by
  intros _ h
  induction h with
  | base => apply Eventually.base; apply hPQ; assumption
  | step hs _ ih =>
    apply Eventually.step hs ih

theorem subsumed_eventually_iff : step.Eventually P ⊑ step.Eventually Q ↔
    P ⊑ step.Eventually Q := by
  constructor
  · intro h _ hP; apply h; apply Eventually.base hP
  · intro h a hE; induction hE with
    | base hP => apply h hP
    | step hs _ ih => apply Eventually.step hs ih

/-! ### Hoare -/

theorem hoare_pre (hP : P' ⊑ P) :
    step.Hoare P Q → step.Hoare P' Q := by
  unfold Hoare; intro h a ha
  apply eventually_mono _ (h (hP ha))
  apply Predicate.subsumed_refl

theorem hoare_post (hQ : Q ⊑ Q') :
    step.Hoare P Q → step.Hoare P Q' := by
  unfold Hoare; intro h a ha
  apply eventually_mono _ (h ha)
  assumption

theorem hoare_def : step.Hoare P Q ↔
    step.Eventually P ⊑ step.Eventually Q := by
  exact subsumed_eventually_iff.symm

theorem hoare_trans :
    step.Hoare P Q → step.Hoare Q R → step.Hoare P R := by
  simp [hoare_def]; intro PQ QR _ _; apply QR; apply PQ; assumption

/-! ### Ensures -/

theorem ensures_pre_empty : step.Ensures .Empty Q C := by
  unfold Ensures Predicate.Empty; intro _ contra; contradiction

theorem ensures_already (hPQ : P ⊑ Q) (hC : Eq ⊑ C) :
    step.Ensures P Q C := by
  unfold Ensures; intro a hP
  apply Eventually.base; constructor
  · apply hPQ hP
  · apply hC; rfl

theorem ensures_pre_post_gen (hP : P' ⊑ P) (hQ : Q ⊑ Q') (hC : C ⊑ C') :
    step.Ensures P Q C → step.Ensures P' Q' C' := by
  unfold Ensures; intro h a ha
  apply eventually_mono _ (h _ (hP ha))
  intro _ ⟨hl, hr⟩; constructor
  · apply hQ hl
  · apply hC hr

theorem ensures_pre_post (hP : P' ⊑ P) (hQ : Q ⊑ Q') :
    step.Ensures P Q C → step.Ensures P' Q' C := by
  apply ensures_pre_post_gen
    (hP := hP) (hQ := hQ) (hC := subsumed_refl _)

theorem ensures_pre_gen (hP : P' ⊑ P) (hC : C ⊑ C') :
    step.Ensures P Q C → step.Ensures P' Q C' := by
  apply ensures_pre_post_gen
    (hP := hP) (hQ := Predicate.subsumed_refl _) (hC := hC)

theorem ensures_pre (hP : P' ⊑ P) :
    step.Ensures P Q C → step.Ensures P' Q C := by
  apply ensures_pre_gen (hP := hP) (hC := subsumed_refl _)

theorem ensures_post_gen (hQ : Q ⊑ Q') (hC : C ⊑ C') :
    step.Ensures P Q C → step.Ensures P Q' C' := by
  apply ensures_pre_post_gen
    (hP := Predicate.subsumed_refl _) (hQ := hQ) (hC := hC)

theorem ensures_post (hQ : Q ⊑ Q') :
    step.Ensures P Q C → step.Ensures P Q' C := by
  apply ensures_post_gen (hQ := hQ) (hC := subsumed_refl _)

theorem ensures_frame (hC : C ⊑ C') :
    step.Ensures P Q C → step.Ensures P Q C' := by
  apply ensures_pre_gen (hP := Predicate.subsumed_refl _) (hC := hC)

theorem ensures_frame_invariant (hJ : ∀ a a', C a a' → J a → J a') :
    step.Ensures P Q C →
    step.Ensures (fun a ↦ P a ∧ J a) (fun a ↦ Q a ∧ J a) C := by
  simp [Ensures]; intro h a hP hJa
  apply eventually_mono _ (h _ hP); intro; simp
  intro hQ hC; exact ⟨⟨hQ, hJ _ _ hC hJa⟩, hC⟩

theorem ensures_trans :
    step.Ensures P Q C → step.Ensures Q R C' →
    step.Ensures P R (C ,, C') := by
  unfold Ensures Seq
  intro hP hQ _ ha; apply subsumed_eventually_iff.mpr _ (hP _ ha)
  intro a' ⟨ha', _⟩; apply eventually_mono _ (hQ _ ha')
  intro _ ⟨_, _⟩; constructor
  · assumption
  · exists a'

end Bignum.Relation
