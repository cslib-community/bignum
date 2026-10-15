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

theorem toNatLE_take (k : Nat) (bs : ByteList) :
    ByteList.toNatLE (bs.take k) = bs.toNatLE % 2^(8 * k) := by
  induction k generalizing bs with
  | zero => simp [toNatLE_nil, Nat.mod_one]
  | succ k ih =>
    cases bs with
    | nil => simp [toNatLE_nil]
    | cons b _ =>
      have h : 2^(8 * k) * 256 = 2^(8 * (k + 1)) := by
        rw [Nat.mul_add, Nat.pow_add]
      simp [toNatLE_cons, ih, ← Nat.mul_mod_mul_right,
        h, b.toNat_add_mod_shift]

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

theorem ofNatLE_mod_cancel (k n : Nat) :
    ByteList.ofNatLE k (n % 256^k) = ByteList.ofNatLE k n := by
  conv => lhs; arg 1; rw [← length_ofNatLE k n]
  rw [← toNatLE_ofNatLE, ofNatLE_toNatLE]

theorem toNatLE_ofNatLE_of_lt (k n : Nat) (h : n < 256^k) :
    ByteList.toNatLE (.ofNatLE k n) = n := by
  simp [toNatLE_ofNatLE, Nat.mod_eq_iff_lt]; assumption

theorem ofIntLE_ofNat (k : Nat) (n : Nat) :
    ByteList.ofIntLE k (.ofNat n) = .ofNatLE k n := by
  rw [ofIntLE, Int.natAbs_emod_of_nonneg] <;> try lia
  simp; apply ofNatLE_mod_cancel

end ByteList

/-! ## Memory -/

namespace Memory
variable {w : Nat} (mem : Memory w) (addr : BitVec w)

/-! ### readBytesLE -/

theorem readBytesLE_zero : mem.readBytesLE addr 0 = [] := by
  rw [readBytesLE]

theorem readBytesLE_succ (k : Nat) :
    mem.readBytesLE addr (k + 1) =
    mem addr :: mem.readBytesLE (addr + 1#w) k := by
  rw [readBytesLE]

theorem readBytesLE_add (k₁ k₂ : Nat) :
    mem.readBytesLE addr (k₁ + k₂) =
    mem.readBytesLE addr k₁ ++ mem.readBytesLE (addr + .ofNat w k₁) k₂ := by
  induction k₁ generalizing addr k₂ with
  | zero => simp [readBytesLE_zero]
  | succ k₁ ih =>
    rw [Nat.add_comm, ← Nat.add_assoc]
    simp [readBytesLE_succ, Nat.add_comm, List.cons_append]
    have h : addr + BitVec.ofNat w (k₁ + 1) = addr + 1#w + .ofNat w k₁ := by
      rw [BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_comm _ 1#w]
    rw [h, ← ih]

theorem length_readBytesLE (k : Nat) :
    (mem.readBytesLE addr k).length = k := by
  induction k generalizing addr with
  | zero => rw [readBytesLE_zero, List.length_nil]
  | succ _ ih => rw [readBytesLE_succ, List.length_cons, ih]

theorem readBytesNatLE_zero :
    mem.readBytesNatLE addr 0 = 0 := by
  rw [readBytesNatLE]

theorem readBytesNatLE_succ (k : Nat) :
    mem.readBytesNatLE addr (k + 1) =
    mem.readBytesNatLE addr k +
      (mem (addr + .ofNat w k)).toNat * 2^(8 * k) := by
  rw [readBytesNatLE]

theorem readBytesNatLE_eq_toNatLE (k : Nat) :
    mem.readBytesNatLE addr k = (mem.readBytesLE addr k).toNatLE := by
  induction k generalizing addr with
  | zero => simp [readBytesLE, readBytesNatLE, ByteList.toNatLE_nil]
  | succ _ ih =>
    rw [readBytesLE_add, ByteList.toNatLE_append,
      readBytesNatLE_succ, ih]
    simp [length_readBytesLE, readBytesLE, ByteList.toNatLE]

theorem readBytesLE_eq_ofNatLE_Nat (k : Nat) :
    mem.readBytesLE addr k =
    .ofNatLE k (mem.readBytesNatLE addr k) := by
  conv => rhs; arg 1; rw [← mem.length_readBytesLE addr k]
  rw [readBytesNatLE_eq_toNatLE, ByteList.ofNatLE_toNatLE]

/-! ### writeBytesLE -/

theorem writeBytesLE_zero (bs : ByteList) :
    mem.writeBytesLE addr 0 bs = mem := by
  rw [writeBytesLE]

theorem writeBytesLE_succ (k : Nat) (bs : ByteList) :
    mem.writeBytesLE addr (k + 1) bs =
    writeBytesLE (fun x => if x = addr then bs.headD 0#8 else mem x)
      (addr + 1#w) k bs.tail := by
  simp [writeBytesLE]

theorem writeBytesLE_succ' (k : Nat) (bs : ByteList) :
    mem.writeBytesLE addr (k + 1) bs =
    (mem.writeBytesLE addr 1 bs).writeBytesLE (addr + 1#w) k bs.tail := by
  simp [writeBytesLE_succ, writeBytesLE_zero]

theorem writeBytesLE_nil (k : Nat) :
    mem.writeBytesLE addr k [] =
    mem.writeBytesLE addr k (.replicate k 0#8) := by
  induction k generalizing mem addr with
  | zero => rfl
  | succ _ ih => simp [writeBytesLE_succ, ih, List.replicate_succ]

theorem writeBytesLE_zero_cons (b : BitVec 8) (bs : ByteList) :
    mem.writeBytesLE addr 0 (b :: bs) = mem := by
  apply writeBytesLE_zero

theorem writeBytesLE_succ_cons (k : Nat) (b : BitVec 8) (bs : ByteList) :
    mem.writeBytesLE addr (k + 1) (b :: bs) =
    (mem.writeBytesLE addr 1 [b]).writeBytesLE (addr + 1#w) k bs := by
  simp [writeBytesLE_succ, writeBytesLE_nil]; rw [writeBytesLE_zero]

theorem writeBytesLE_cons (k : Nat) (b : BitVec 8) (bs : ByteList) :
    mem.writeBytesLE addr k (b :: bs) =
    if k = 0 then mem
    else (mem.writeBytesLE addr 1 [b]).writeBytesLE
      (addr + 1) k.pred bs := by
  cases _ : k with
  | zero => apply writeBytesLE_zero_cons
  | succ _ => apply writeBytesLE_succ_cons

theorem writeBytesLE_append (k : Nat) (bs₁ bs₂ : ByteList) :
    mem.writeBytesLE addr k (bs₁ ++ bs₂) =
    (mem.writeBytesLE addr (min k bs₁.length) bs₁).writeBytesLE
      (addr + .ofNat w (min k bs₁.length)) (k - bs₁.length) bs₂ := by
  induction bs₁ generalizing mem addr k bs₂ with
  | nil => simp [writeBytesLE_zero]
  | cons _ _ ih =>
    cases k with
    | zero => simp [writeBytesLE_zero]
    | succ _ =>
      simp; rw [writeBytesLE_succ_cons, ih]
      conv =>
        rhs; rw [writeBytesLE_succ_cons, BitVec.ofNat_add]; arg 2
        rw [BitVec.add_comm _ 1#w, ← BitVec.add_assoc]

theorem writeBytesLE_take (k : Nat) (bs : ByteList) :
    mem.writeBytesLE addr k (bs.take k) = mem.writeBytesLE addr k bs := by
  induction bs generalizing mem addr k with
  | nil => simp
  | cons _ _ ih =>
    cases k with
    | zero => apply writeBytesLE_zero
    | succ _ =>
      rw [writeBytesLE_cons, writeBytesLE_cons, writeBytesLE_succ_cons]
      simp [writeBytesLE_zero]; rw [← ih, ← writeBytesLE_succ_cons]

-- theorem writeBytesLE_take_padright (k : Nat) (bs : ByteList) :
--     mem.writeBytesLE addr k ((bs.take k).rightpad (k - bs.length) 0#8) =
--     mem.writeBytesLE addr k bs := by
--   unfold List.rightpad; simp
--   induction bs generalizing mem addr k with
--   | nil => simp [writeBytesLE_nil]
--   | cons b bs' ih =>
--     cases k with
--     | zero => simp [writeBytesLE_zero]
--     | succ k' =>
--       simp
--       conv => lhs; rw [writeBytesLE_succ_cons]
--       conv => rhs; rw [writeBytesLE_succ_cons, ← ih]
--       simp [Nat.min_def]
--       by_cases h : k' ≤ bs'.length
--       · simp [h]
--       · conv => lhs; arg 4; rw [ite_eq_right h, Nat.sub_add_eq]
--         conv => rhs; arg 4; rw [ite_eq_right h]
--         sorry

theorem writeBytesLE_add (k₁ k₂ : Nat) (bs : ByteList) :
    mem.writeBytesLE addr (k₁ + k₂) bs =
    (mem.writeBytesLE addr k₁ bs).writeBytesLE
      (addr + .ofNat w k₁) k₂ (bs.drop k₁) := by
  induction k₁ generalizing mem addr k₂ bs with
  | zero => simp [writeBytesLE_zero]
  | succ _ ih =>
    conv => lhs; rw [Nat.add_assoc, Nat.add_comm 1, ih, writeBytesLE_succ']
    simp [ih, BitVec.ofNat_add, BitVec.add_assoc]

theorem writeBytesNatLE'_zero (n : Nat) :
    mem.writeBytesNatLE' addr 0 n = mem := by
  rw [writeBytesNatLE']

theorem writeBytesNatLE'_succ (k n : Nat) :
    mem.writeBytesNatLE' addr (k + 1) n =
    writeBytesNatLE' (fun x => if x = addr + .ofNat w k
        then .ofNat 8 (n / 2^(8 * k) % 256) else mem x) addr k n := by
  simp [writeBytesNatLE']

theorem writeBytesNatLE'_succ' (k n : Nat) :
    mem.writeBytesNatLE' addr (k + 1) n =
    (mem.writeBytesNatLE'
      (addr + .ofNat w k) 1 (n / 2^(8 * k))).writeBytesNatLE' addr k n := by
  simp [writeBytesNatLE']

theorem writeBytesNatLE'_succ'' (k n : Nat) (hk : k < 2^w) :
    writeBytesNatLE' mem addr (k + 1) n =
    writeBytesNatLE'
      (fun x ↦ if x == addr then .ofNat 8 (n % 256) else mem x)
      (addr + 1#w) k (n / 256) := by
  induction k generalizing mem addr n with
  | zero => simp [writeBytesNatLE']
  | succ k ih =>
    rw [writeBytesNatLE', ih _ _ _ (by omega), writeBytesNatLE'_succ]
    congr; funext x
    have ha : addr + 1#w + .ofNat w k = addr + .ofNat w (k + 1) := by
      rw [BitVec.ofNat_add, addr.add_assoc, BitVec.add_comm 1#w]
    let fk : Fin (2^w) := ⟨k + 1, hk⟩
    have hne := addr.add_ofNat_ne_self fk (by simp [fk])
    by_cases hx : x = addr
    · simp [hx, fk, hne.symm, ha]
    · by_cases hx' : x = addr + BitVec.ofNat w (k + 1)
      · simp [hx', fk, hne, ha]; rw [Nat.div_div_eq_div_mul,
          Nat.mul_comm 256, Nat.mul_add, Nat.pow_add]
      · simp [hx', ha]

theorem writeBytesNatLE_zero (n : Nat) :
    mem.writeBytesNatLE addr 0 n = mem := by
  rw [writeBytesNatLE]

theorem writeBytesNatLE_succ (k n : Nat) :
    mem.writeBytesNatLE addr (k + 1) n =
    writeBytesNatLE (fun x => if x = addr then .ofNat 8 (n % 256) else mem x)
      (addr + 1#w) k (n / 256) := by
  simp [writeBytesNatLE]

theorem writeBytesNatLE_succ' (k n : Nat) :
    mem.writeBytesNatLE addr (k + 1) n =
    (mem.writeBytesNatLE addr 1 n).writeBytesNatLE
      (addr + 1#w) k (n / 256) := by
  simp [writeBytesNatLE]

theorem writeBytesNatLE_mod_cancel (k n : Nat) :
    mem.writeBytesNatLE addr k (n % 2^(8 * k)) =
    mem.writeBytesNatLE addr k n := by
  induction k generalizing mem addr n with
  | zero => simp [writeBytesNatLE_zero]
  | succ k ih =>
    have e₁ : 2^(8 * k) * 256 = 2^(8 * (k + 1)) := by
      rw [Nat.mul_add, Nat.pow_add]
    have e₂ : mem.writeBytesNatLE addr 1 (n % (2^(8 * k) * 256))
        = mem.writeBytesNatLE addr 1 n := by
      simp [e₁, writeBytesNatLE]
      funext x; by_cases h : x = addr <;> simp [h]; congr 1;
      rw [Nat.mod_mod_of_dvd]; rw [← e₁]; apply Nat.dvd_mul_left
    rw [writeBytesNatLE_succ', ← e₁, Nat.mod_mul_left_div_self, ih]
    rw [e₂, ← writeBytesNatLE_succ']

theorem writeBytesNatLE_add (k₁ k₂ : Nat) (n : Nat) :
    mem.writeBytesNatLE addr (k₁ + k₂) n =
    (mem.writeBytesNatLE addr k₁ n).writeBytesNatLE
      (addr + .ofNat w k₁) k₂ (n / 2^(8 * k₁)) := by
  induction k₁ generalizing mem addr k₂ n with
  | zero => simp [writeBytesNatLE_zero]
  | succ _ ih =>
    conv => lhs; rw [Nat.add_comm _ 1, Nat.add_assoc, Nat.add_comm,
      writeBytesNatLE_succ', ih, BitVec.add_assoc,
      BitVec.add_comm 1#w, ← BitVec.ofNat_add]
    conv => rhs; rw [writeBytesNatLE_succ']
    rw [show 256 = 2^8 from rfl, Nat.div_div_eq_div_mul,
        ← Nat.pow_add', Nat.mul_add]

theorem writeBytesNatLE_toNatLE_eq (k : Nat) (bs : ByteList) :
    mem.writeBytesNatLE addr k bs.toNatLE =
    mem.writeBytesLE addr k bs := by
  induction k generalizing mem addr bs with
  | zero => simp [writeBytesLE, writeBytesNatLE]
  | succ _ ih =>
    rw [writeBytesLE_succ', writeBytesNatLE_succ',
      ← ih, ByteList.toNatLE_tail]; congr; rw [writeBytesLE_succ,
      writeBytesLE_zero, writeBytesNatLE_succ,
      writeBytesNatLE_zero, bs.headD_zero]

theorem writeBytesLE_ofNatLE_eq (k n : Nat) :
    mem.writeBytesLE addr k (.ofNatLE k n) =
    mem.writeBytesNatLE addr k n := by
  induction k generalizing mem addr n with
  | zero => rw [writeBytesNatLE_zero, writeBytesLE_zero]
  | succ _ ih =>
    rw [writeBytesNatLE_succ', writeBytesLE_succ', ← ih]
    conv => lhs; arg 4; rw [ByteList.ofNatLE_succ, List.tail_cons]
    congr; rw [writeBytesNatLE_succ, writeBytesNatLE_zero,
      writeBytesLE_succ, writeBytesLE_zero, ByteList.ofNatLE_succ,
      List.headD_cons, BitVec.ofNat_mod_cancel]

theorem writeBytesNatLE'_eq (k n : Nat) (hk : k ≤ 2^w) :
    mem.writeBytesNatLE' addr k n =
    mem.writeBytesNatLE addr k n := by
  induction k generalizing mem addr n with
  | zero => simp [writeBytesNatLE', writeBytesNatLE]
  | succ k ih =>
    rw [mem.writeBytesNatLE'_succ'' _ _ _ hk, writeBytesNatLE]
    apply ih; omega

theorem writeBytesNatLE'_toNatLE_eq (k : Nat) (bs : ByteList) (hk : k ≤ 2^w) :
    mem.writeBytesNatLE' addr k bs.toNatLE =
    mem.writeBytesLE addr k bs := by
  rw [writeBytesNatLE'_eq _ _ _ _ hk]
  apply writeBytesNatLE_toNatLE_eq

theorem writeBytesLE_ofNatLE_eq' (k n : Nat) (hk : k ≤ 2^w) :
    mem.writeBytesLE addr k (.ofNatLE k n) =
    mem.writeBytesNatLE' addr k n := by
  rw [writeBytesNatLE'_eq _ _ _ _ hk]
  apply writeBytesLE_ofNatLE_eq

-- theorem readBytesLE_writeBytesLE
--     (addr : BitVec w) (k : Nat) (bs : ByteList) :
--     (mem.writeBytesLE addr k bs).readBytesLE addr k =
--     (bs.take k).rightpad (k - bs.length) 0#8 := by
--   sorry

end Memory
end Bignum
