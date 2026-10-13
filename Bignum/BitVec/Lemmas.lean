/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/

module

public import Bignum.BitVec.Basic

@[expose] public section

/-! # More lemmas about bitvectors -/

set_option autoImplicit false

namespace BitVec

theorem ofNat_mod_cancel {w : Nat} (n : Nat) :
    BitVec.ofNat w (n % 2^w) = BitVec.ofNat w n := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat]

theorem ofNat_mod_cancel_of_ge {w : Nat} (n m : Nat) (h : m ≥ w):
    BitVec.ofNat w (n % 2^m) = BitVec.ofNat w n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow _ h)

theorem toNat_add_mod_shift (b : BitVec 8) (n k : Nat) :
    b.toNat + n * 256 % 2^(8 * (k + 1)) =
    (b.toNat + n * 256) % 2^(8 * (k + 1)) := by
  have h : 2^(8 * (k + 1)) = 256 * 2^(8 * k) := by
    rw [Nat.mul_add_one, Nat.pow_add, Nat.mul_comm]
  rw [h, Nat.mul_comm n, ← Nat.add_mod_mod, Nat.mul_mod_mul_left]
  symm; apply Nat.mod_eq_of_lt; omega

theorem setLsb_getLsb {w : Nat} (x : BitVec w) (i j : Fin w) (b : Bool) :
    (x.setLsb i b).getLsb j = if i = j then b else x.getLsb j := by
  unfold setLsb; cases b <;> by_cases h : i = j <;>
  simp [h] <;> rcases Fin.lt_or_lt_of_ne h <;> lia

theorem overwriteLsb'_extractLsb'_low {w : Nat} (start len : Nat)
    (x : BitVec w) (y : BitVec len) :
    (x.overwriteLsb' start len y).extractLsb' 0 start =
    x.extractLsb' 0 start := by
  simp only [overwriteLsb', setWidth_append]
  by_cases h₁ : w ≤ start <;> simp [h₁]
  · rw [setWidth_extractLsb'_of_le h₁, extractLsb'_eq_self]
  · by_cases h₂ : w ≤ len + start <;>
    simp [h₂, extractLsb'_cast, extractLsb'_append_eq_ite] <;>
    intro <;> subst start <;> simp

theorem overwriteLsb'_extractLsb'_mid {w : Nat} (start len : Nat)
    (x : BitVec w) (y : BitVec len) :
    (x.overwriteLsb' start len y).extractLsb' start len =
    (y.extractLsb' 0 (w - start)).setWidth len := by
  -- TODO: Remove grind.
  simp only [overwriteLsb', setWidth_append]; grind

theorem overwriteLsb'_extractLsb'_high {w : Nat} (start len : Nat)
    (x : BitVec w) (y : BitVec len) :
    (x.overwriteLsb' start len y).extractLsb' (start + len) w =
    x.extractLsb' (start + len) w := by
  -- TODO: Remove grind.
  simp only [overwriteLsb', setWidth_append]; grind

end BitVec
