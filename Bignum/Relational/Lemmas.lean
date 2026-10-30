/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Bignum.Relational.Basic

@[expose] public section

/-! # Lemmas about relations and Hoare-type rules -/

/-! ## Set -/

namespace Bignum.Set

universe u

variable {α : Type u}

theorem empty_subset (p : Set α) : ∅ ⊆ p := by
  intro _ _; contradiction

theorem subset_full (p : Set α) : p ⊆ .Full :=
  fun _ _ ↦ True.intro

theorem subset_refl (p : Set α) : p ⊆ p :=
  fun _ h ↦ h

instance : @Std.Refl (Set α) (· ⊆ ·) where
  refl r := subset_refl r

theorem subset_antisymm (p q : Set α) : p ⊆ q → q ⊆ p → p = q := by
  intro ab ba; funext; exact propext ⟨@ab _, @ba _⟩

instance : @Std.Antisymm (Set α) (· ⊆ ·) where
  antisymm p q := subset_antisymm p q

theorem subset_trans (p q r : Set α) : p ⊆ q → q ⊆ r → p ⊆ r :=
  fun ab cd _ ha ↦ cd (ab ha)

end Bignum.Set

/-! ## Rel -/

namespace Bignum.Rel

universe u₁ u₂ u₃ u₄
variable {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄}

/-! ### Subset (⊆) -/

theorem empty_subset (r : Rel α β) : ∅ ⊆ r := by
  intro _ _ _; contradiction

theorem subset_full (r : Rel α β) : r ⊆ .Full :=
  fun _ _ _ ↦ True.intro

theorem subset_refl (r : Rel α β) : r ⊆ r :=
  fun _ _ h ↦ h

instance : @Std.Refl (Rel α β) (· ⊆ ·) where
  refl r := subset_refl r

theorem subset_antisymm (r s : Rel α β) : r ⊆ s → s ⊆ r → r = s := by
  intro ab ba; funext; apply propext ⟨@ab _ _, @ba _ _⟩

instance : @Std.Antisymm (Rel α β) (· ⊆ ·) where
  antisymm r s := subset_antisymm r s

theorem subsumed_trans (r s t : Rel α β) : r ⊆ s → s ⊆ t → r ⊆ t :=
  fun ab cd _ _ ha ↦ cd (ab ha)

/-! ### Seq (,,) -/

theorem seq_assoc (r : Rel α β) (s : Rel β γ) (t : Rel γ δ) :
    r ,, s ,, t = (r ,, s) ,, t := by
  ext a d; constructor
  · intro ⟨b, ab, c, bc, cd⟩; exact ⟨c, ⟨b, ab, bc⟩, cd⟩
  · intro ⟨c, ⟨b, ab, bc⟩, cd⟩; exact ⟨b, ab, c, bc, cd⟩

theorem seq_eq_left (r : Rel α β) : Eq ,, r = r := by
  ext a b; constructor
  · intro ⟨_, h, _⟩; rw [h]; assumption
  · intro; exists a

theorem seq_eq_right (r : Rel α β) : r ,, Eq = r := by
  ext a b; constructor
  · intro ⟨_, _, h⟩; rw [← h]; assumption
  · intro; exists b

theorem seq_full_full [Inhabited β] : @.Full α β ,, @.Full β γ = .Full := by
  unfold Seq Full; simp

theorem subset_seq_seq (r s : Rel α β) (t₁ t₂ : Rel β γ) :
    r ⊆ s → t₁ ⊆ t₂ → r ,, t₁ ⊆ s ,, t₂ := by
  simp [Subset, Seq]; exact fun hr ht a c b ab bc ↦ ⟨b, hr ab, ht bc⟩

theorem subset_seq_left (r s t : Rel α α) :
    r ⊆ t → s ⊆ t → t ,, t = t → r ,, s ⊆ t := by
  simp [Subset, Seq]; intro rt st tt _ _ c ac cb; rw [← tt]
  exact ⟨c, rt ac, st cb⟩

theorem subset_eq_seq (r s : Rel α α) :
    Eq ⊆ r → Eq ⊆ s → Eq ⊆ r ,, s := by
  simp [Subset, Seq]; exact fun hr hs a ↦ ⟨a, @hr _, @hs _⟩

theorem subset_seq_eq_right (r s : Rel α β) (rb : Rel β β) :
    r ⊆ s → Eq ⊆ rb → r ⊆ s ,, rb := by
  simp [Subset, Seq]; exact fun hl hr _ b ab ↦ ⟨b, hl ab, @hr _⟩

theorem subset_seq_eq_left (r s : Rel α β) (ra : Rel α α) :
    Eq ⊆ ra → r ⊆ s → r ⊆ ra ,, s := by
  simp [Subset, Seq]; exact fun hl hr a _ ab ↦ ⟨a, @hl _, hr ab⟩

/-! ### Eventually -/

variable {step : Rel α α}
variable {P P' Q Q' R J : Set α} {C C' : Rel α α}

theorem eventually_mono : P ⊆ Q → step.Eventually P ⊆ step.Eventually Q := by
  intros PQ _ h
  induction h with
  | base => apply Eventually.base; apply PQ; assumption
  | step _ hs _ ih =>
    apply Eventually.step _ hs ih

theorem subsumed_eventually_iff : step.Eventually P ⊆ step.Eventually Q ↔
    P ⊆ step.Eventually Q := by
  constructor
  · intro h _ hP; apply h; apply Eventually.base _ hP
  · intro h a hE; induction hE with
    | base _ hP => apply h hP
    | step _ hs _ ih => apply Eventually.step _ hs ih

/-! ### Hoare -/

theorem hoare_pre : P' ⊆ P → step.Hoare P Q → step.Hoare P' Q :=
  fun hP hH _ ha ↦ hH (hP ha)

theorem hoare_post (hQ : Q ⊆ Q') : step.Hoare P Q → step.Hoare P Q' :=
  fun h _ ha ↦ step.eventually_mono hQ (h ha)

theorem hoare_def : step.Hoare P Q ↔ step.Eventually P ⊆ step.Eventually Q :=
  subsumed_eventually_iff.symm

theorem hoare_trans :
    step.Hoare P Q → step.Hoare Q R → step.Hoare P R := by
  simp [hoare_def]; intro PQ QR _ _; apply QR; apply PQ; assumption

/-! ### Ensures -/

theorem ensures_pre_empty : step.Ensures ∅ Q C := by
  intro _ _; contradiction

theorem ensures_already : P ⊆ Q → Eq ⊆ C → step.Ensures P Q C := by
  intro hPQ hC _ hP; apply Eventually.base; constructor
  · apply hPQ hP
  · apply hC; rfl

theorem ensures_pre_post_gen (hP : P' ⊆ P) (hQ : Q ⊆ Q') (hC : C ⊆ C') :
    step.Ensures P Q C → step.Ensures P' Q' C' := by
  intro h a ha
  apply step.eventually_mono _ (h _ (hP ha))
  intro _ ⟨hl, hr⟩; constructor
  · apply hQ hl
  · apply hC hr

theorem ensures_pre_post (hP : P' ⊆ P) (hQ : Q ⊆ Q') :
    step.Ensures P Q C → step.Ensures P' Q' C := by
  apply ensures_pre_post_gen (hP := hP) (hQ := hQ) (hC := C.subset_refl)

theorem ensures_pre_gen (hP : P' ⊆ P) (hC : C ⊆ C') :
    step.Ensures P Q C → step.Ensures P' Q C' := by
  apply ensures_pre_post_gen (hP := hP) (hQ := Q.subset_refl) (hC := hC)

theorem ensures_pre (hP : P' ⊆ P) :
    step.Ensures P Q C → step.Ensures P' Q C := by
  apply ensures_pre_gen (hP := hP) (hC := C.subset_refl)

theorem ensures_post_gen (hQ : Q ⊆ Q') (hC : C ⊆ C') :
    step.Ensures P Q C → step.Ensures P Q' C' := by
  apply ensures_pre_post_gen (hP := P.subset_refl) (hQ := hQ) (hC := hC)

theorem ensures_post (hQ : Q ⊆ Q') :
    step.Ensures P Q C → step.Ensures P Q' C := by
  apply ensures_post_gen (hQ := hQ) (hC := subset_refl _)

theorem ensures_frame (hC : C ⊆ C') :
    step.Ensures P Q C → step.Ensures P Q C' := by
  apply ensures_pre_gen (hP := P.subset_refl) (hC := hC)

theorem ensures_frame_invariant (hJ : ∀ a a', C a a' → J a → J a') :
    step.Ensures P Q C → step.Ensures (P ∩ J) (Q ∩ J) C := by
  simp [Ensures]; intro h a ⟨hP, hJa⟩
  apply step.eventually_mono _ (h _ hP); intro; simp
  intro hQ hC; exact ⟨⟨hQ, hJ _ _ hC hJa⟩, hC⟩

theorem ensures_trans :
    step.Ensures P Q C → step.Ensures Q R C' →
    step.Ensures P R (C ,, C') := by
  unfold Ensures Seq
  intro hP hQ _ ha; apply subsumed_eventually_iff.mpr _ (hP _ ha)
  intro a' ⟨ha', _⟩; apply step.eventually_mono _ (hQ _ ha')
  intro _ ⟨_, _⟩; constructor
  · assumption
  · exists a'

end Bignum.Rel
