/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/

module

import Batteries.Data.Nat
import Bignum.BitVec

public import Bignum.Memory.Basic

@[expose] public section

/-! # Lemmas about memory operations -/

set_option autoImplicit false

namespace Bignum

/-! ## Byte list -/

namespace ByteList

theorem toNatLE_nil : ByteList.toNatLE [] = 0 := by
  rfl

theorem toNatLE_cons (b : BitVec 8) (bs : ByteList) :
    ByteList.toNatLE (b :: bs) = b.toNat + bs.toNatLE * 256 := by
  rw [toNatLE, List.foldr_cons, ← toNatLE, Nat.shiftLeft_eq]

theorem toNatLE_lt (bs : ByteList) : bs.toNatLE < 256 ^ bs.length := by
  unfold toNatLE
  conv => lhs; arg 1; intro _ _; rw [Nat.shiftLeft_eq]; simp
  induction bs with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldr_cons, List.length_cons, Nat.pow_add_one (m:=bs.length),
      Nat.mul_comm _ 256, Nat.mul_comm _ 256]
    have h : b.toNat < 2 ^ 8 := by
      apply BitVec.toNat_lt_twoPow_of_le; decide
    apply Nat.add_mul_lt_mul_of_lt_of_lt <;> assumption

theorem ofNatLE_zero (n : Nat) : ByteList.ofNatLE 0 n = [] := by
  rfl

theorem ofNatLE_succ (k n : Nat) : ByteList.ofNatLE k.succ n
    = BitVec.ofNat 8 n :: ByteList.ofNatLE k (n / 256) := by
  rw [ofNatLE]; congr; rw [Nat.shiftRight_eq_div_pow]

theorem length_ofNatLE (k n : Nat) : (ofNatLE k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ _ ih => rw [ofNatLE, List.length_cons, ih]

theorem length_ofIntLE (k : Nat) (n : Int) : (ofIntLE k n).length = k := by
  rw [ofIntLE, length_ofNatLE]

theorem ofNatLE_toNatLE (bs : ByteList) :
    .ofNatLE bs.length bs.toNatLE = bs := by
  induction bs with
  | nil => simp [ofNatLE]
  | cons b bs ih =>
    rw [List.length_cons, ofNatLE_succ, toNatLE_cons]
    simp [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.ofNat_mul]
    rw [Nat.add_div (by decide), BitVec.toNat_mod_cancel]; simp
    have h256 : 256 = 2 ^ 8 := by rfl
    have h : (b.toNat / 256 = 0) ∧ (if 256 ≤ b.toNat then 1 else 0) = 0 := by
      and_intros <;> simp <;> rw [h256] <;>
        apply BitVec.toNat_lt_twoPow_of_le <;> simp
    simp [h.left, h.right]; assumption

theorem toNatLE_ofNatLE_zero (k : Nat) :
    ByteList.toNatLE (.ofNatLE k 0) = 0 := by
  induction k with
  | zero => rfl
  | succ _ ih => simp [ofNatLE_succ, toNatLE_cons, ih]

theorem toNatLE_ofNatLE (k n : Nat) :
    ByteList.toNatLE (.ofNatLE k n) = n % 256 ^ k := by
  induction k generalizing n with
  | zero => rw [ofNatLE_zero, toNatLE_nil, Nat.mod_one]
  | succ _ ih => simp [ofNatLE_succ, toNatLE_cons, ih,
      Nat.mul_comm, ← Nat.mod_mul, Nat.pow_succ]

theorem ofNatLE_mod (k n : Nat) :
    ByteList.ofNatLE k (n % 256 ^ k) = ByteList.ofNatLE k n := by
  conv => lhs; arg 1; rw [← length_ofNatLE k n]
  rw [← toNatLE_ofNatLE, ofNatLE_toNatLE]

theorem toNatLE_ofNatLE_of_lt (k n : Nat) (h : n < 256 ^ k) :
    ByteList.toNatLE (.ofNatLE k n) = n := by
  simp [toNatLE_ofNatLE, Nat.mod_eq_iff_lt]; assumption

theorem ofIntLE_ofNat (k : Nat) (n : Nat) :
    ByteList.ofIntLE k (.ofNat n) = .ofNatLE k n := by
  rw [ofIntLE, Int.natAbs_emod_of_nonneg] <;> try lia
  simp; rw [ofNatLE_mod]

end ByteList
end Bignum
