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

theorem toNatLE_append (bs₁ bs₂ : ByteList) :
    ByteList.toNatLE (bs₁ ++ bs₂) =
    bs₁.toNatLE + bs₂.toNatLE * 2 ^ (8 * bs₁.length) := by
  induction bs₁ generalizing bs₂ with
  | nil => simp [toNatLE_nil]
  | cons _ _ ih =>
    simp [List.cons_append, toNatLE_cons, Nat.add_assoc,
      ih, Nat.add_mul, Nat.mul_add, Nat.pow_add, Nat.mul_assoc]

theorem toNatLE_lt (bs : ByteList) : bs.toNatLE < 256^bs.length := by
  unfold toNatLE
  conv => lhs; arg 1; intro _ _; rw [Nat.shiftLeft_eq]; simp
  induction bs with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldr_cons, List.length_cons, Nat.pow_add_one (m:=bs.length),
      Nat.mul_comm _ 256, Nat.mul_comm _ 256]
    have h : b.toNat < 2^8 := by
      apply BitVec.toNat_lt_twoPow_of_le; decide
    apply Nat.add_mul_lt_mul_of_lt_of_lt <;> assumption

theorem ofNatLE_zero (n : Nat) : ByteList.ofNatLE 0 n = [] := by
  rfl

theorem ofNatLE_succ (k n : Nat) :
    ByteList.ofNatLE k.succ n =
    BitVec.ofNat 8 n :: ByteList.ofNatLE k (n / 256) := by
  rw [ofNatLE]; congr; apply Nat.shiftRight_eq_div_pow

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
    have h256 : 256 = 2^8 := by rfl
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
    ByteList.toNatLE (.ofNatLE k n) = n % 256^k := by
  induction k generalizing n with
  | zero => rw [ofNatLE_zero, toNatLE_nil, Nat.mod_one]
  | succ _ ih => simp [ofNatLE_succ, toNatLE_cons, ih,
      Nat.mul_comm, ← Nat.mod_mul, Nat.pow_succ]

theorem ofNatLE_mod (k n : Nat) :
    ByteList.ofNatLE k (n % 256^k) = ByteList.ofNatLE k n := by
  conv => lhs; arg 1; rw [← length_ofNatLE k n]
  rw [← toNatLE_ofNatLE, ofNatLE_toNatLE]

theorem toNatLE_ofNatLE_of_lt (k n : Nat) (h : n < 256^k) :
    ByteList.toNatLE (.ofNatLE k n) = n := by
  simp [toNatLE_ofNatLE, Nat.mod_eq_iff_lt]; assumption

theorem ofIntLE_ofNat (k : Nat) (n : Nat) :
    ByteList.ofIntLE k (.ofNat n) = .ofNatLE k n := by
  rw [ofIntLE, Int.natAbs_emod_of_nonneg] <;> try lia
  simp; apply ofNatLE_mod

end ByteList

/-! ## Memory -/

namespace Memory
variable {w : Nat} (mem : Memory w)

theorem read_bytesLE_zero (addr : BitVec w) :
    mem.read_bytesLE addr 0 = [] := by
  rw [read_bytesLE]

theorem read_bytesLE_succ (addr : BitVec w) (k : Nat) :
    mem.read_bytesLE addr (k + 1) =
    mem addr :: mem.read_bytesLE (addr + 1#w) k := by
  rw [read_bytesLE]

theorem read_bytesLE_add (addr : BitVec w) (n m : Nat) :
    mem.read_bytesLE addr (n + m) =
    mem.read_bytesLE addr n ++ mem.read_bytesLE (addr + .ofNat w n) m := by
  induction n generalizing addr m with
  | zero => simp [read_bytesLE_zero]
  | succ n ih =>
    rw [Nat.add_comm, ← Nat.add_assoc,
      read_bytesLE_succ, Nat.add_comm,
      read_bytesLE_succ, List.cons_append]
    have h : addr + BitVec.ofNat w (n + 1) = addr + 1#w + .ofNat w n := by
      rw [BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_comm _ 1#w]
    rw [h, ← ih]

theorem length_read_bytesLE (addr : BitVec w) (k : Nat) :
    (mem.read_bytesLE addr k).length = k := by
  induction k generalizing addr with
  | zero => rw [read_bytesLE_zero, List.length_nil]
  | succ _ ih => rw [read_bytesLE_succ, List.length_cons, ih]

theorem read_bytesLE_asNat_zero (addr : BitVec w) :
    mem.read_bytesLE_asNat addr 0 = 0 := by
  rw [read_bytesLE_asNat]

theorem read_bytesLE_asNat_succ (addr : BitVec w) (k : Nat) :
    mem.read_bytesLE_asNat addr (k + 1) =
    (mem (addr + .ofNat _ k)).toNat * 2^(8 * k) +
      mem.read_bytesLE_asNat addr k := by
  rw [read_bytesLE_asNat]

theorem read_bytesLE_toNatLE_eq_asNat (addr : BitVec w) (k : Nat) :
    (mem.read_bytesLE addr k).toNatLE = mem.read_bytesLE_asNat addr k := by
  induction k generalizing addr with
  | zero => simp [read_bytesLE, read_bytesLE_asNat, ByteList.toNatLE_nil]
  | succ _ ih =>
    rw [read_bytesLE_add, ByteList.toNatLE_append,
      read_bytesLE_asNat_succ, ih]
    conv => rhs; rw [Nat.add_comm]
    congr; simp [length_read_bytesLE]

theorem write_bytesLE_zero (addr : BitVec w) (bs : ByteList) :
    mem.write_bytesLE addr 0 bs = mem := by
  rw [write_bytesLE]

theorem write_bytesLE_succ (addr : BitVec w) (k : Nat) (bs : ByteList) :
    mem.write_bytesLE addr (k + 1) bs =
    write_bytesLE (λ x ↦
      if x = addr then bs.headD 0#8 else mem x) (addr + 1#w) k bs.tail := by
  simp [write_bytesLE]

theorem write_bytesLE_succ' (addr : BitVec w) (k : Nat) (bs : ByteList) :
    mem.write_bytesLE addr (k + 1) bs =
    (mem.write_bytesLE addr 1 bs).write_bytesLE (addr + 1#w) k bs.tail := by
  simp [write_bytesLE_succ, write_bytesLE_zero]

theorem write_bytesLE_nil (addr : BitVec w) (k : Nat) :
    mem.write_bytesLE addr k [] =
    mem.write_bytesLE addr k (.replicate k 0#8) := by
  induction k generalizing mem addr with
  | zero => rfl
  | succ _ ih => simp [write_bytesLE_succ, ih, List.replicate_succ]

theorem write_bytesLE_zero_cons
    (addr : BitVec w) (b : BitVec 8) (bs : ByteList) :
    mem.write_bytesLE addr 0 (b :: bs) = mem := by
  apply write_bytesLE_zero

theorem write_bytesLE_succ_cons
    (addr : BitVec w) (k : Nat) (b : BitVec 8) (bs : ByteList) :
    mem.write_bytesLE addr (k + 1) (b :: bs) =
    (mem.write_bytesLE addr 1 [b]).write_bytesLE (addr + 1#w) k bs := by
  simp [write_bytesLE_succ, write_bytesLE_nil]; rw [write_bytesLE_zero]

theorem write_bytesLE_cons
    (addr : BitVec w) (k : Nat) (b : BitVec 8) (bs : ByteList) :
    mem.write_bytesLE addr k (b :: bs) =
    if k = 0 then mem
    else (mem.write_bytesLE addr 1 [b]).write_bytesLE (addr + 1) k.pred bs := by
  cases _ : k with
  | zero => apply write_bytesLE_zero_cons
  | succ _ => apply write_bytesLE_succ_cons

theorem write_bytesLE_take (addr : BitVec w) (k : Nat) (bs : ByteList) :
    mem.write_bytesLE addr k bs = mem.write_bytesLE addr k (bs.take k) := by
  induction bs generalizing mem addr k with
  | nil => simp
  | cons _ _ ih =>
    cases h : k with
    | zero => apply write_bytesLE_zero
    | succ _ =>
      rw [write_bytesLE_cons, write_bytesLE_cons, write_bytesLE_succ_cons]
      simp [write_bytesLE_zero]; rw [ih, ← write_bytesLE_succ_cons, ← h]

theorem write_bytesLE_asNat_zero (addr : BitVec w) (n : Nat) :
    mem.write_bytesLE_asNat addr 0 n = mem := by
  rw [write_bytesLE_asNat]

theorem write_bytesLE_asNat_succ (addr : BitVec w) (k n : Nat) :
    mem.write_bytesLE_asNat addr (k + 1) n =
    write_bytesLE_asNat (λ x ↦ if x = addr + .ofNat _ k
        then .ofNat 8 (n / 2^(8 * k) % 256) else mem x) addr k n := by
  simp [write_bytesLE_asNat]

theorem write_bytesLE_asNat_succ' (addr : BitVec w) (k n : Nat) :
    mem.write_bytesLE_asNat addr (k + 1) n =
    (mem.write_bytesLE_asNat
      (addr + .ofNat _ k) 1 (n / 2^(8 * k) % 256)).write_bytesLE_asNat
        addr k n := by
  simp [write_bytesLE_asNat_succ, write_bytesLE_asNat_zero]

theorem write_bytesLE_add (addr : BitVec w) (n m : Nat) (bs : ByteList) :
    mem.write_bytesLE addr (n + m) bs =
    (mem.write_bytesLE addr n bs).write_bytesLE
      (addr + .ofNat _ n) m (bs.drop n) := by
  induction n generalizing mem addr m bs with
  | zero => simp [write_bytesLE_zero]
  | succ _ ih =>
    conv => lhs; rw [Nat.add_assoc, Nat.add_comm 1, ih, write_bytesLE_succ']
    simp [ih, BitVec.ofNat_add, BitVec.add_assoc]

-- theorem write_bytesLE_succ'' (addr : BitVec w) (k : Nat) (bs : ByteList) :
--     mem.write_bytesLE addr (k + 1) bs =
--     write_bytesLE (λ x ↦
--       if x = addr + .ofNat _ k
--       then (bs.getD k 0#8) else mem x) addr k bs := by
--   induction k generalizing mem addr bs with
--   | zero =>
--     simp only [write_bytesLE_zero, write_bytesLE_succ]
--     rw [List.headD_eq_getD]; simp
--   | succ k ih =>
--     conv => lhs; rw [write_bytesLE_succ, ih]
--     conv => rhs; rw []
--     sorry

-- theorem write_bytesLE_eq_asNat (addr : BitVec w) (k : Nat) (bs : ByteList) :
--     mem.write_bytesLE addr k bs =
--     mem.write_bytesLE_asNat addr k (bs.toNatLE) := by
--   induction k generalizing mem addr bs with
--   | zero => simp [write_bytesLE, write_bytesLE_asNat]
--   | succ k ih =>
--     conv => lhs; rw [write_bytesLE_add, ih]
--     conv => rhs; rw [write_bytesLE_asNat_succ', ← ih]
--     simp [write_bytesLE_asNat_succ, write_bytesLE_asNat_zero, ← ih]
--     rw [← write_bytesLE_add]
--     sorry

end Memory
end Bignum
