/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/

module

public import Bignum.BitVec.Basic

@[expose] public section

/-! # More lemmas about bitvectors -/

namespace BitVec

theorem ofNat_mod_cancel {w : Nat} (n : Nat) :
    BitVec.ofNat w (n % 2^w) = BitVec.ofNat w n := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat]

theorem ofNat_mod_cancel_of_ge {w : Nat} (n m : Nat) (h : m ≥ w):
    BitVec.ofNat w (n % 2^m) = BitVec.ofNat w n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow _ h)

theorem add_ofNat_ne_self
    {w : Nat} (x : BitVec w) (m : Fin (2^w)) (hpos : m ≠ 0) :
    x + .ofNat w m ≠ x := by
  intro contra; have h := congrArg BitVec.toNat contra
  have hgt : 0 < m := by
    apply Nat.ne_zero_iff_zero_lt.mp (Fin.val_ne_zero_iff.mpr hpos)
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt m.isLt] at h
  rcases Nat.lt_or_ge (x.toNat + m) (2^w) with (hl | hr)
  · rw [Nat.mod_eq_of_lt hl] at h; omega
  · rw [Nat.mod_eq_sub_mod hr, Nat.mod_eq_of_lt (by omega)] at h; omega

theorem toNat_add_mod_shift {w : Nat} (x : BitVec w) (n k : Nat) :
    x.toNat + n * 2^w % 2^(w * (k + 1)) =
    (x.toNat + n * 2^w) % 2^(w * (k + 1)) := by
  have h : 2^(w * (k + 1)) = 2^w * 2^(w * k) := by
    simp [Nat.mul_add, Nat.pow_add, Nat.mul_comm]
  rw [h, Nat.mul_comm n, ← Nat.add_mod_mod, Nat.mul_mod_mul_left]
  symm; apply Nat.mod_eq_of_lt; calc
    x.toNat + 2^w * (n % 2^(w * k))
      < 2^w + 2^w * (n % 2^(w * k)) := by omega
    _ = 2^w * ((n % 2^(w * k)) + 1) := by rw [Nat.mul_succ]; omega
    _ ≤ 2^w * 2^(w * k) := by
      have hpos : 0 < 2^(w * k) := Nat.pow_pos (by decide)
      exact Nat.mul_le_mul_left _ (Nat.mod_lt _ hpos)

theorem setLsb_getLsb {w : Nat} (x : BitVec w) (i j : Fin w) (b : Bool) :
    (x.setLsb i b).getLsb j = if i = j then b else x.getLsb j := by
  rw [setLsb]; cases b <;> by_cases h : i = j <;>
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
