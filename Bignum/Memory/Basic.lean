/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Bignum.Component

@[expose] public section

/-! # Memory operations -/

set_option autoImplicit false

namespace Bignum

/-! ## Byte list -/

abbrev ByteList := List (BitVec 8)

namespace ByteList

/--
Converts a little-endian byte list `bs` to a natural number.
-/
def toNatLE (bs : ByteList) : Nat :=
  bs.foldr (λ b n ↦ b.toNat + n <<< 8) 0

/--
Converts a natural number `n` to a little-endian byte list of `len` bytes.
Truncates the list to `len` bytes if `n` is too large.
-/
def ofNatLE (len n : Nat) : ByteList :=
  match len with
  | 0 => []
  | k + 1 => .ofNat 8 n :: ofNatLE k (n >>> 8)

/--
Converts an integer `n` to a little-endian byte list of `len` bytes.
Truncates the list to `len` bytes if `n` is too small or too large.
-/
def ofIntLE (len : Nat) (n : Int) : ByteList :=
  ofNatLE len $ Int.natAbs (n % 256^len)

end ByteList

/-! ## Byte-addressable memory -/

abbrev Memory (w : Nat) := BitVec w → BitVec 8

namespace Memory

/--
Reads `len` bytes from memory starting at offset `addr`.
Returns the little-endian encoded result as a byte list.
-/
def read_bytesLE
    {w : Nat} (mem : Memory w) (addr : BitVec w) (len : Nat) : ByteList :=
  match len with
  | 0 => []
  | k + 1 => mem addr :: mem.read_bytesLE (addr + 1#w) k

/--
Reads `len` bytes from memory starting at offset `addr`.
Returns the little-endian encoded result as a natural number.
-/
def read_bytesLE_asNat
    {w : Nat} (mem : Memory w) (addr : BitVec w) (len : Nat) : Nat :=
  match len with
  | 0 => 0
  | k + 1 => (mem (addr + .ofNat _ k)).toNat * 2 ^ (8 * k)
      + mem.read_bytesLE_asNat addr k

/--
Writes `len` bytes from `bs` to memory starting at offset `addr`.
Assumes that `bs` is little-endian encoded.  Returns the updated memory.
-/
def write_bytesLE
    {w : Nat} (mem : Memory w) (addr : BitVec w) (len : Nat) (bs : ByteList) :
    Memory w :=
  match len with
  | 0 => mem
  | k + 1 => let mem' := λ x ↦ if x == addr then bs.headD 0 else mem x
      write_bytesLE mem' (addr + 1#w) k bs.tail

/--
Writes `len` bytes from `n` to memory starting at offset `addr`.
Assumes that `n` is little-endian encoded.  Returns the updated memory.
-/
def write_bytesLE_asNat
    {w : Nat} (mem : Memory w) (addr : BitVec w) (len : Nat) (n : Nat) :
    Memory w :=
  match len with
  | 0 => mem
  | k + 1 => let mem' := λ x ↦ if x == addr + .ofNat w k
                               then .ofNat 8 (n / 2^(8 * k) % 2^8) else mem x
      write_bytesLE_asNat mem' addr k n

end Memory
end Bignum
