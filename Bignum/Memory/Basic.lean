/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

@[expose] public section

/-! # Memory operations -/

set_option autoImplicit false

namespace Bignum

/-! ## Byte list -/

/-- List of bytes. -/
abbrev ByteList := List (BitVec 8)

namespace ByteList

/--
Converts a little-endian byte list `bs` to a natural number.
-/
def toNatLE (bs : ByteList) : Nat :=
  bs.foldr (fun b n ↦ b.toNat + n <<< 8) 0

/--
Converts a natural number `n` to a little-endian byte list of `len` bytes.
Truncates the list to `len` bytes if `n` is too large.
-/
def ofNatLE (len n : Nat) : ByteList :=
  match len with
  | 0 => []
  | k + 1 => .ofNat 8 n :: ofNatLE k (n >>> 8)

/--
Converts an integer `i` to a little-endian byte list of `len` bytes.
Truncates the list to `len` bytes if `i` is too small or too large.
-/
def ofIntLE (len : Nat) (i : Int) : ByteList :=
  ofNatLE len $ Int.natAbs (i % 256^len)

end ByteList

/-! ## Byte-addressable memory -/

/-- Mapping of addresses to bytes. -/
abbrev Memory (w : Nat) := BitVec w → BitVec 8

namespace Memory

/-- The all zeros memory. -/
def allZeros {w : Nat} : Memory w :=
  fun _ ↦ 0#8

/-- The all ones memory. -/
def allOnes {w : Nat} : Memory w :=
  fun _ ↦ .allOnes 8

/--
Reads `len` bytes from memory starting at offset `addr`.
Returns a little-endian byte list.
-/
def readBytesLE
    {w : Nat} (mem : Memory w) (addr : BitVec w) (len : Nat) : ByteList :=
  match len with
  | 0 => []
  | k + 1 => mem addr :: mem.readBytesLE (addr + 1#w) k

/--
Reads `len` bytes from memory starting at offset `addr`.
Returns a little-endian encoded natural number.

This definition corresponds to the read method s2n-bignum's `bytes`.
-/
def readBytesNatLE
    {w : Nat} (mem : Memory w) (addr : BitVec w) (len : Nat) : Nat :=
  match len with
  | 0 => 0
  | k + 1 =>
    mem.readBytesNatLE addr k +
      (mem (addr + .ofNat _ k)).toNat * 2^(8 * k)

/--
Writes `len` bytes from `bs` to memory starting at offset `addr`.
Assumes that `bs` is little-endian encoded.  Returns the updated memory.
-/
def writeBytesLE
    {w : Nat} (mem : Memory w) (addr : BitVec w) (len : Nat) (bs : ByteList) :
    Memory w :=
  match len with
  | 0 => mem
  | k + 1 =>
    writeBytesLE
      (fun x ↦ if x == addr then bs.headD 0#8 else mem x)
      (addr + 1#w) k bs.tail

/--
Writes `len` bytes from `n` to memory starting at offset `addr`.
Assumes that `n` is little-endian encoded.  Returns the updated memory.

This definition corresponds to the write method of s2n-bignum's `bytes`.
Notice that the writing is done in reverse order, i.e., from the end to the
beginning of the address space (from `addr+k` to `addr`).  We cannot prove
that this function is equivalent to `writeBytesLE` or `writeBytesNatLE`,
unless we assume `len ≤ 2^w`.  See `writeBytesNatLE'_eq`.
-/
def writeBytesNatLE' {w : Nat}
    (mem : Memory w) (addr : BitVec w) (len : Nat) (n : Nat) :
    Memory w :=
  match len with
  | 0 => mem
  | k + 1 =>
    writeBytesNatLE' (fun x ↦
        if x == addr + .ofNat _ k
        then .ofNat 8 (n / 2^(8 * k) % 2^8)
        else mem x)
      addr k n

/--
Alternative version of `writeBytesNatLE'` which performs the writing in
direct order, from the beginning to the end of the address space.  This
function is equivalent to `writeBytesLE ∘ ByteList.ofNat`.
-/
def writeBytesNatLE {w : Nat}
    (mem : Memory w) (addr : BitVec w) (len : Nat) (n : Nat) :
    Memory w :=
  match len with
  | 0 => mem
  | k + 1 =>
    writeBytesNatLE
      (fun x ↦ if x == addr then .ofNat 8 (n % 256) else mem x)
      (addr + 1#w) k (n / 256)

/--
Asserts that byte list `bs` is loaded on memory at address `addr`.
-/
def BytesLoadedLE {w : Nat}
    (mem : Memory w) (addr : BitVec w) (bs : ByteList) : Prop :=
  mem.readBytesLE addr bs.length = bs

/--
Tests whether byte list `bs` is loaded on memory at address `addr`.
-/
def bytesLoadedLE {w : Nat}
    (mem : Memory w) (addr : BitVec w) (bs : ByteList) : Bool :=
  mem.readBytesLE addr bs.length == bs

theorem bytesLoadedLE_iff {w : Nat} (mem : Memory w) (addr : BitVec w)
    (bs : ByteList) :
    mem.bytesLoadedLE addr bs ↔ mem.BytesLoadedLE addr bs := by
  unfold bytesLoadedLE BytesLoadedLE; constructor
  · exact eq_of_beq
  · intro h; simp [h]

instance {w : Nat} (mem : Memory w) (addr : BitVec w) (bs : ByteList) :
    Decidable (BytesLoadedLE mem addr bs) :=
  decidable_of_iff (bytesLoadedLE mem addr bs)
    (bytesLoadedLE_iff mem addr bs)

/--
Asserts that byte list `bs` is loaded at 4-byte aligned address `addr`.
-/
structure AlignedBytesLoadedLE {w : Nat}
    (mem : Memory w) (addr : BitVec w) (bs : ByteList) : Prop where
  /-- Address `addr` is 4-byte aligned. -/
  aligned : (4 ∣ addr.toNat)
  /-- Byte list `bs` is loaded at address `addr`. -/
  loaded : mem.BytesLoadedLE addr bs

/--
Tests whether byte list `bs` is loaded at 4-byte aligned address `addr`.
-/
def alignedBytesLoadedLE {w : Nat}
    (mem : Memory w) (addr : BitVec w) (bs : ByteList) : Bool :=
  (4 ∣ addr.toNat) && mem.bytesLoadedLE addr bs

theorem alignedBytesLoadedLE_iff {w : Nat}
    (mem : Memory w) (addr : BitVec w) (bs : ByteList) :
    mem.alignedBytesLoadedLE addr bs ↔
    mem.AlignedBytesLoadedLE addr bs := by
  simp [alignedBytesLoadedLE]; constructor <;> intro ⟨hl, hr⟩
  · exact ⟨hl, (mem.bytesLoadedLE_iff _ _).mp hr⟩
  · exact ⟨hl, (mem.bytesLoadedLE_iff _ _ ).mpr hr⟩

instance {w : Nat} (mem : Memory w) (addr : BitVec w) (bs : ByteList) :
    Decidable (AlignedBytesLoadedLE mem addr bs) :=
  decidable_of_iff (alignedBytesLoadedLE mem addr bs)
    (alignedBytesLoadedLE_iff mem addr bs)

end Memory
end Bignum
