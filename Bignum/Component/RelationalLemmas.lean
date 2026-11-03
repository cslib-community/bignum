/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Bignum.Component.Extra
public import Bignum.Component.Relational

@[expose] public section

/-! # Lemmas about relations and Hoare-type rules -/

namespace Bignum.Component

universe u₁ u₂ u₃ u₄
variable {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄}

theorem seq_preserves_component (cp : Component α β)
    (r : Rel α α) (t : Rel α α) (a a' : α)
    (hr : ∀ x y, r x y → cp.read x = cp.read y)
    (ht : ∀ x y, t x y → cp.read x = cp.read y) :
    (r ,, t) a a' → cp.read a' = cp.read a := by
  intro ⟨x, hax, hxa'⟩; rw [hr _ _ hax, ht _ _ hxa']

/-! ## Assign (≔) -/

theorem assign_func (cp : Component α β) (a a₁ a₂ : α) (b : β) :
    (cp ≔ b) a a₁ → (cp ≔ b) a a₂ → a₁ = a₂ := fun ha₁ ha₂ ↦ ha₁ ▸ ha₂

theorem seq_assign (cp : Component α β) (b : β) (r : Rel α β) (a : α) :
    ((cp ≔ b) ,, r) a = r (cp.write b a) := by
  unfold Rel.Seq Assign; simp

theorem assign_zerotop8 (cp : Component α (BitVec 16)) (bv : BitVec 8) :
    ((cp :> .zerotop8) ≔ bv) = (cp ≔ bv.zeroExtend 16) := by
  unfold Assign; simp [compose, through, zerotop8]

theorem assign_zerotop16 (cp : Component α (BitVec 32)) (bv : BitVec 16) :
    ((cp :> .zerotop16) ≔ bv) = (cp ≔ bv.zeroExtend 32) := by
  unfold Assign; simp [compose, through, zerotop16]

theorem assign_zerotop32 (cp : Component α (BitVec 64)) (bv : BitVec 32) :
    ((cp :> .zerotop32) ≔ bv) = (cp ≔ bv.zeroExtend 64) := by
  unfold Assign; simp [compose, through, zerotop32]

theorem assign_zerotop64 (cp : Component α (BitVec 128)) (bv : BitVec 64) :
    ((cp :> .zerotop64) ≔ bv) = (cp ≔ bv.zeroExtend 128) := by
  unfold Assign; simp [compose, through, zerotop64]

theorem assign_zerotop128 (cp : Component α (BitVec 256)) (bv : BitVec 128) :
    ((cp :> .zerotop128) ≔ bv) = (cp ≔ bv.zeroExtend 256) := by
  unfold Assign; simp [compose, through, zerotop128]

theorem assign_zerotop256 (cp : Component α (BitVec 512)) (bv : BitVec 256) :
    ((cp :> .zerotop256) ≔ bv) = (cp ≔ bv.zeroExtend 512) := by
  unfold Assign; simp [compose, through, zerotop256]

/-! ## Assigns -/

theorem assigns_def (cp : Component α β) :
    cp.Assigns = fun a a' ↦ ∃ b, cp.write b a = a' := by
  rfl

theorem assigns_refl (cp : Component α β) [h : cp.WriteOverRead] (a : α) :
    cp.Assigns a a := by
  rw [assigns_def]; exists cp.read a; apply h.write_over_read

instance (cp : Component α β) [cp.WriteOverRead] : Std.Refl cp.Assigns where
  refl a := cp.assigns_refl a

theorem seq_assigns (cp : Component α β) (r : Rel α β) :
    (cp.Assigns ,, r) = fun a a' ↦ ∃ b, r (cp.write b a) a' := by
  unfold Rel.Seq Assigns Assign; funext a b; grind

theorem subset_assigns_compose
    (cp₁ : Component α β) (cp₂ : Component β γ) (cp₂' : Component β δ) :
    cp₂.Assigns ⊆ cp₂'.Assigns →
    (cp₁ :> cp₂).Assigns ⊆ (cp₁ :> cp₂').Assigns := by
  simp [Subset, assigns_def]; intro h a c
  rcases @h (cp₁.read a) c with ⟨d, hd⟩
  exists d; simp [compose, hd]

theorem subset_assigns_compose_left
    (cp₁ : Component α β) (cp₂ : Component β γ) :
    (cp₁ :> cp₂).Assigns ⊆ cp₁.Assigns := by
  simp [Subset, assigns_def, compose]

/-! ## MayChange -/

theorem mayChange_nil (a : α) :
    MayChange (.nil : List (Component α β)) a a := by
  rw [MayChange]

theorem mayChange_singleton (cp : Component α β) :
    MayChange [cp] = Assigns cp :=
  Rel.seq_eq_right _

theorem ensures_mayChange_preserved
    (cp : Component α β) [h : cp.ExtensionallyValid]
    (step : Rel α α) (P Q : Set α) (R : Rel α α)
    (hR : R ⊆ (cp.read · = cp.read ·)) :
    (∀ b, step.Ensures
      (P ∩ (cp.read · = b)) (Q ∩ (cp.read · = b)) (R ,, MayChange [cp])) →
    step.Ensures P Q R := by
  simp [Rel.Ensures, mayChange_singleton, assigns_def]; intro hE a hP
  apply step.eventually_mono _ (hE (cp.read a) ⟨hP, rfl⟩)
  intro x ⟨⟨hQ, hxa⟩, y, ⟨Raa, ⟨b, _⟩⟩⟩; subst x
  refine ⟨hQ, ?_⟩; suffices hy : y = (cp.write b y) from hy ▸ Raa
  rw [← h.write_over_read (cp.write b y), hxa, hR Raa,
    h.write_over_write, h.write_over_read]

end Bignum.Component
