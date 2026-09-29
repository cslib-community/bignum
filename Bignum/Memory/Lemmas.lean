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

theorem toNatLE_bound (l : ByteList) : l.toNatLE < 256 ^ l.length := by
  unfold toNatLE
  conv => lhs; arg 1; intro _ _; rw [Nat.shiftLeft_eq]; simp
  induction l with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldr_cons, List.length_cons, Nat.pow_add_one (m:=bs.length),
      Nat.mul_comm _ 256, Nat.mul_comm _ 256]
    have h : b.toNat < 2 ^ 8 := by
      apply BitVec.toNat_lt_twoPow_of_le; decide
    apply Nat.add_mul_lt_mul_of_lt_of_lt <;> assumption

theorem ofNatLE_zero (n : Nat) : ByteList.ofNatLE 0 n = [] := by
  rfl

theorem ofNatLE_succ (m n : Nat) :
    ByteList.ofNatLE m.succ n
    = BitVec.ofNat 8 n :: ByteList.ofNatLE m (n / 256) := by
  rw [ofNatLE]; congr; rw [Nat.shiftRight_eq_div_pow]

theorem length_ofNatLE (m n : Nat) :
    (ofNatLE m n).length = m := by
  induction m generalizing n with
  | zero => rfl
  | succ _ ih => rw [ofNatLE, List.length_cons, ih]

theorem length_ofIntLE (m : Nat) (n : Int) :
    (ofIntLE m n).length = m := by
  rw [ofIntLE, length_ofNatLE]

theorem ofNatLE_toNatLE (bs : ByteList) :
    ByteList.ofNatLE (bs.length) bs.toNatLE = bs := by
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

end ByteList
end Bignum
