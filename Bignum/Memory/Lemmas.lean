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
  rw [toNatLE, bs.foldr_cons, ← toNatLE, Nat.shiftLeft_eq]

theorem toNatLE_head (bs : ByteList) (h : bs ≠ []) :
    ByteList.toNatLE [bs.head h] = bs.toNatLE % 256 := by
  cases bs with
  | nil => contradiction
  | cons b _ => simp [toNatLE_cons, toNatLE_nil,
      show 256 = 2^8 from rfl, b.toNat_mod_cancel]

theorem headD_zero (bs : ByteList) :
    bs.headD 0#8 = .ofNat 8 (bs.toNatLE % 256) := by
  cases bs <;> simp [toNatLE_nil, show 256 = 2^8 from rfl,
    toNatLE_cons, BitVec.toNat_mod_cancel _]

theorem toNatLE_tail (bs : ByteList) :
    ByteList.toNatLE bs.tail = bs.toNatLE / 256 := by
  cases bs with
  | nil => simp [toNatLE_nil]
  | cons b _ => simp [toNatLE_cons,
      Nat.add_mul_div_right _ _ (Nat.zero_lt_succ _), b.isLt]

theorem toNatLE_append (bs₁ bs₂ : ByteList) :
    ByteList.toNatLE (bs₁ ++ bs₂) =
    bs₁.toNatLE + bs₂.toNatLE * 2^(8 * bs₁.length) := by
  induction bs₁ generalizing bs₂ with
  | nil => simp [toNatLE_nil]
  | cons _ _ ih => simp [List.cons_append, toNatLE_cons, Nat.add_assoc,
      ih, Nat.add_mul, Nat.mul_add, Nat.pow_add, Nat.mul_assoc]

theorem toNatLE_lt (bs : ByteList) : bs.toNatLE < 256^bs.length := by
  unfold toNatLE; conv => lhs; arg 1; intro _ _; rw [Nat.shiftLeft_eq]; simp
  induction bs with
  | nil => simp
  | cons b bs ih =>
    rw [bs.foldr_cons, bs.length_cons, Nat.pow_add_one (m:=bs.length),
      Nat.mul_comm _ 256, Nat.mul_comm _ 256]
    have h : b.toNat < 2^8 := by
      apply b.toNat_lt_twoPow_of_le; decide
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
    rw [bs.length_cons, ofNatLE_succ, toNatLE_cons]
    simp [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.ofNat_mul]
    rw [Nat.add_div (by decide), BitVec.toNat_mod_cancel]; simp
    have h : b.toNat / 256 = 0 ∧ (if 256 ≤ b.toNat then 1 else 0) = 0 := by
      and_intros <;> simp <;> rw [show 256 = 2^8 from rfl] <;>
        apply b.toNat_lt_twoPow_of_le <;> simp
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

/-! ### read_bytesLE -/

theorem read_bytesLE_zero (addr : BitVec w) :
    mem.read_bytesLE addr 0 = [] := by
  rw [read_bytesLE]

theorem read_bytesLE_succ (addr : BitVec w) (k : Nat) :
    mem.read_bytesLE addr (k + 1) =
    mem addr :: mem.read_bytesLE (addr + 1#w) k := by
  rw [read_bytesLE]

theorem read_bytesLE_add (addr : BitVec w) (k₁ k₂ : Nat) :
    mem.read_bytesLE addr (k₁ + k₂) =
    mem.read_bytesLE addr k₁ ++ mem.read_bytesLE (addr + .ofNat w k₁) k₂ := by
  induction k₁ generalizing addr k₂ with
  | zero => simp [read_bytesLE_zero]
  | succ k₁ ih =>
    rw [Nat.add_comm, ← Nat.add_assoc,
      read_bytesLE_succ, Nat.add_comm,
      read_bytesLE_succ, List.cons_append]
    have h : addr + BitVec.ofNat w (k₁ + 1) = addr + 1#w + .ofNat w k₁ := by
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
    mem.read_bytesLE_asNat addr k +
      (mem (addr + .ofNat w k)).toNat * 2^(8 * k) := by
  rw [read_bytesLE_asNat]

theorem read_bytesLE_asNat_eq (addr : BitVec w) (k : Nat) :
    mem.read_bytesLE_asNat addr k = (mem.read_bytesLE addr k).toNatLE := by
  induction k generalizing addr with
  | zero => simp [read_bytesLE, read_bytesLE_asNat, ByteList.toNatLE_nil]
  | succ _ ih =>
    rw [read_bytesLE_add, ByteList.toNatLE_append,
      read_bytesLE_asNat_succ, ih]
    simp [length_read_bytesLE, read_bytesLE, ByteList.toNatLE]

theorem read_bytesLE_eq_asNat (addr : BitVec w) (k : Nat) :
    mem.read_bytesLE addr k =
    ByteList.ofNatLE k (mem.read_bytesLE_asNat addr k) := by
  conv => rhs; arg 1; rw [← length_read_bytesLE mem addr k]
  rw [read_bytesLE_asNat_eq, ByteList.ofNatLE_toNatLE]

/-! ### write_bytesLE -/

theorem write_bytesLE_zero (addr : BitVec w) (bs : ByteList) :
    mem.write_bytesLE addr 0 bs = mem := by
  rw [write_bytesLE]

theorem write_bytesLE_succ (addr : BitVec w) (k : Nat) (bs : ByteList) :
    mem.write_bytesLE addr (k + 1) bs =
    write_bytesLE (fun x => if x = addr then bs.headD 0#8 else mem x)
      (addr + 1#w) k bs.tail := by
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
    else (mem.write_bytesLE addr 1 [b]).write_bytesLE
      (addr + 1) k.pred bs := by
  cases _ : k with
  | zero => apply write_bytesLE_zero_cons
  | succ _ => apply write_bytesLE_succ_cons

theorem write_bytesLE_take (addr : BitVec w) (k : Nat) (bs : ByteList) :
    mem.write_bytesLE addr k (bs.take k) = mem.write_bytesLE addr k bs := by
  induction bs generalizing mem addr k with
  | nil => simp
  | cons _ _ ih =>
    cases h : k with
    | zero => apply write_bytesLE_zero
    | succ _ =>
      rw [write_bytesLE_cons, write_bytesLE_cons, write_bytesLE_succ_cons]
      simp [write_bytesLE_zero]; rw [← ih, ← write_bytesLE_succ_cons, ← h]

theorem write_bytesLE_add (addr : BitVec w) (k₁ k₂ : Nat) (bs : ByteList) :
    mem.write_bytesLE addr (k₁ + k₂) bs =
    (mem.write_bytesLE addr k₁ bs).write_bytesLE
      (addr + .ofNat w k₁) k₂ (bs.drop k₁) := by
  induction k₁ generalizing mem addr k₂ bs with
  | zero => simp [write_bytesLE_zero]
  | succ _ ih =>
    conv => lhs; rw [Nat.add_assoc, Nat.add_comm 1, ih, write_bytesLE_succ']
    simp [ih, BitVec.ofNat_add, BitVec.add_assoc]

theorem write_bytesLE_comm₁
    (addr₁ addr₂ : BitVec w) (bs₁ bs₂ : ByteList) (h : addr₁ ≠ addr₂) :
    (mem.write_bytesLE addr₁ 1 bs₁).write_bytesLE addr₂ 1 bs₂ =
    (mem.write_bytesLE addr₂ 1 bs₂).write_bytesLE addr₁ 1 bs₁ := by
  simp only [write_bytesLE_succ, write_bytesLE_zero]
  ext addr _ _; by_cases ha : addr = addr₁ <;> simp [ha, h]

theorem write_bytesLE_asNat_zero (addr : BitVec w) (n : Nat) :
    mem.write_bytesLE_asNat addr 0 n = mem := by
  rw [write_bytesLE_asNat]

theorem write_bytesLE_asNat_succ (addr : BitVec w) (k n : Nat) :
    mem.write_bytesLE_asNat addr (k + 1) n =
    write_bytesLE_asNat (fun x => if x = addr + .ofNat w k
        then .ofNat 8 (n / 2^(8 * k) % 256) else mem x) addr k n := by
  simp [write_bytesLE_asNat]

theorem write_bytesLE_asNat_succ' (addr : BitVec w) (k n : Nat) :
    mem.write_bytesLE_asNat addr (k + 1) n =
    (mem.write_bytesLE_asNat
      (addr + .ofNat w k) 1 (n / 2^(8 * k) % 256)).write_bytesLE_asNat
        addr k n := by
  simp [write_bytesLE_asNat_succ, write_bytesLE_asNat_zero]

-- theorem write_bytesLE_asNat_add (addr : BitVec w) (k₁ k₂ : Nat) (n : Nat) :
--     mem.write_bytesLE_asNat addr (k₁ + k₂) n =
--     (mem.write_bytesLE_asNat addr k₁ n).write_bytesLE_asNat
--       (addr + .ofNat w k₁) k₂ (n / 2^(8 * k₁)) := by
--    sorry

theorem write_bytesLE_asNat'_zero (addr : BitVec w) (n : Nat) :
    mem.write_bytesLE_asNat' addr 0 n = mem := by
  rw [write_bytesLE_asNat']

theorem write_bytesLE_asNat'_succ (addr : BitVec w) (k n : Nat) :
    mem.write_bytesLE_asNat' addr (k + 1) n =
    write_bytesLE_asNat'
      (fun x => if x = addr then .ofNat 8 (n % 256) else mem x)
      (addr + 1#w) k (n / 256) := by
  simp [write_bytesLE_asNat']

theorem write_bytesLE_asNat'_succ' (addr : BitVec w) (k n : Nat) :
    mem.write_bytesLE_asNat' addr (k + 1) n =
    (mem.write_bytesLE_asNat' addr 1 n).write_bytesLE_asNat'
      (addr + 1#w) k (n / 256) := by
  simp [write_bytesLE_asNat']

theorem write_bytesLE_asNat'_add (addr : BitVec w) (k₁ k₂ : Nat) (n : Nat) :
    mem.write_bytesLE_asNat' addr (k₁ + k₂) n =
    (mem.write_bytesLE_asNat' addr k₁ n).write_bytesLE_asNat'
      (addr + .ofNat w k₁) k₂ (n / 2^(8 * k₁)) := by
  induction k₁ generalizing mem addr k₂ n with
  | zero => simp [write_bytesLE_asNat'_zero]
  | succ _ ih =>
    conv => lhs; rw [Nat.add_comm _ 1, Nat.add_assoc, Nat.add_comm,
      write_bytesLE_asNat'_succ', ih, BitVec.add_assoc,
      BitVec.add_comm 1#w, ← BitVec.ofNat_add]
    conv => rhs; rw [write_bytesLE_asNat'_succ']
    rw [show 256 = 2^8 from rfl, Nat.div_div_eq_div_mul,
        ← Nat.pow_add', Nat.mul_add]

theorem write_bytesLE_eq_asNat' (addr : BitVec w) (k : Nat) (bs : ByteList) :
    mem.write_bytesLE addr k bs =
    mem.write_bytesLE_asNat' addr k bs.toNatLE := by
  induction k generalizing mem addr bs with
  | zero => simp [write_bytesLE, write_bytesLE_asNat']
  | succ _ ih =>
    rw [write_bytesLE_succ', write_bytesLE_asNat'_succ',
      ih, ByteList.toNatLE_tail]
    congr; rw [write_bytesLE_succ, write_bytesLE_zero,
      write_bytesLE_asNat'_succ, write_bytesLE_asNat'_zero]
    rw [bs.headD_zero]

theorem write_bytesLE_asNat'_eq (addr : BitVec w) (k n : Nat) :
    mem.write_bytesLE_asNat' addr k n =
    mem.write_bytesLE addr k (.ofNatLE k n) := by
  induction k generalizing mem addr n with
  | zero => rw [write_bytesLE_asNat'_zero, write_bytesLE_zero]
  | succ _ ih =>
    rw [write_bytesLE_asNat'_succ', write_bytesLE_succ', ih]
    conv => rhs; arg 4; rw [ByteList.ofNatLE_succ, List.tail_cons]
    congr; rw [write_bytesLE_asNat'_succ, write_bytesLE_asNat'_zero,
      write_bytesLE_succ, write_bytesLE_zero, ByteList.ofNatLE_succ,
      List.headD_cons, BitVec.ofNat_mod]

-- theorem write_bytesLE_asNat'_eq_asNat (addr : BitVec w) (k n : Nat) :
--     mem.write_bytesLE_asNat' addr k n =
--     mem.write_bytesLE_asNat addr k n := by
--   induction k generalizing mem addr n with
--   | zero => rw [write_bytesLE_asNat', write_bytesLE_asNat]
--   | succ k ih =>
--     sorry

end Memory
end Bignum
