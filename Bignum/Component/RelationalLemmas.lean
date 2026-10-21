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

theorem Seq_preserves_component (cp : Component α β)
    (r : Relation α α) (t : Relation α α) (a a' : α)
    (hr : ∀ x y, r x y → cp.read x = cp.read y)
    (ht : ∀ x y, t x y → cp.read x = cp.read y) :
    (r ,, t) a a' → cp.read a' = cp.read a := by
  unfold Relation.Seq; intro ⟨x, hax, hxa'⟩; rw [hr _ _ hax, ht _ _ hxa']

/-! ## Assign (≔) -/

theorem Seq_Assign (cp : Component α β) (b : β) (r : Relation α β) (a : α) :
    ((cp ≔ b) ,, r) a = r (cp.write b a) := by
  unfold Relation.Seq Assign; simp

theorem Assign_zerotop8 (cp : Component α (BitVec 16)) (bv : BitVec 8) :
    ((cp :> .zerotop8) ≔ bv) = (cp ≔ bv.zeroExtend 16) := by
  unfold Assign; simp [compose, through, zerotop8]

theorem Assign_zerotop16 (cp : Component α (BitVec 32)) (bv : BitVec 16) :
    ((cp :> .zerotop16) ≔ bv) = (cp ≔ bv.zeroExtend 32) := by
  unfold Assign; simp [compose, through, zerotop16]

theorem Assign_zerotop32 (cp : Component α (BitVec 64)) (bv : BitVec 32) :
    ((cp :> .zerotop32) ≔ bv) = (cp ≔ bv.zeroExtend 64) := by
  unfold Assign; simp [compose, through, zerotop32]

theorem Assign_zerotop64 (cp : Component α (BitVec 128)) (bv : BitVec 64) :
    ((cp :> .zerotop64) ≔ bv) = (cp ≔ bv.zeroExtend 128) := by
  unfold Assign; simp [compose, through, zerotop64]

theorem Assign_zerotop128 (cp : Component α (BitVec 256)) (bv : BitVec 128) :
    ((cp :> .zerotop128) ≔ bv) = (cp ≔ bv.zeroExtend 256) := by
  unfold Assign; simp [compose, through, zerotop128]

theorem Assign_zerotop256 (cp : Component α (BitVec 512)) (bv : BitVec 256) :
    ((cp :> .zerotop256) ≔ bv) = (cp ≔ bv.zeroExtend 512) := by
  unfold Assign; simp [compose, through, zerotop256]

/-! ## Assigns -/

theorem Assigns_def (cp : Component α β) :
    cp.Assigns = fun a a' ↦ ∃ b, cp.write b a = a' := by
  unfold Assigns Assign; rfl

theorem Seq_Assigns (cp : Component α β) (r : Relation α β) :
    (cp.Assigns ,, r) = fun a a' ↦ ∃ b, r (cp.write b a) a' := by
  unfold Relation.Seq Assigns Assign; funext a b; grind

theorem Eq_Subsumed_Assigns (cp : Component α β)
    [h : cp.ExtensionallyValid] :
    Eq ⊑ cp.Assigns := by
  simp [Assigns, Assign, Relation.Subsumed]; intro a
  exists cp.read a; apply h.write_over_read

theorem Assigns_compose_Subsumed_Assings_compose
    (cp₁ : Component α β) (cp₂ : Component β γ) (cp₂' : Component β δ)
    (h : cp₂.Assigns ⊑ cp₂'.Assigns) :
    (cp₁ :> cp₂).Assigns ⊑ (cp₁ :> cp₂').Assigns := by
  simp [Assigns_def, Relation.Subsumed] at *
  intro a c; rcases h (cp₁.read a) c with ⟨d, h'⟩
  exists d; simp [compose, h']

theorem Assigns_compose_Subsumed_Assings
    (cp₁ : Component α β) (cp₂ : Component β γ) :
    (cp₁ :> cp₂).Assigns ⊑ cp₁.Assigns := by
  simp [compose, Relation.Subsumed, Assigns_def]

/-! ## MayChange -/

theorem MayChange_nil (a : α) :
    MayChange (.nil : List (Component α β)) a a := by
  rw [MayChange]

theorem MayChange_singleton (cp : Component α β) :
    MayChange [cp] = Assigns cp := by
  simp [MayChange, Relation.Seq_Eq_right]

end Bignum.Component
