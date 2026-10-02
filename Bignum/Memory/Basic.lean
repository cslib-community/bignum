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
Truncates the list if `n` is too large.
-/
def ofNatLE (len n : Nat) : ByteList :=
  match len with
  | 0 => []
  | len + 1 => BitVec.ofNat 8 n :: ByteList.ofNatLE len (n >>> 8)

/--
Converts an integer `n` to a little-endian byte list of `len` bytes.
Truncates the list to `len` bytes if `n` is too small or large.
-/
def ofIntLE (len : Nat) (n : Int) : ByteList :=
  ofNatLE len $ Int.natAbs (n % 256^len)

end ByteList

/-! ## Byte-addressable memory -/

abbrev Memory (w : Nat) := BitVec w → BitVec 8

namespace Memory

/--
Reads `len` bytes from `memory` starting at offset `addr`.
Returns a little-endian byte list.
-/
def read_bytesLE
    {w : Nat} (mem : Memory w) (addr : BitVec w) (len : Nat) : ByteList :=
  match len with
  | 0 => []
  | len + 1 => mem addr :: mem.read_bytesLE (addr + 1#w) len

/--
Reads `len` bytes from `memory` starting at offset `addr`.
Returns the little-endian encoded result a natural number.
-/
def read_bytesLE_asNat
    {w : Nat} (mem : Memory w) (addr : BitVec w) (len : Nat) : Nat :=
  match len with
  | 0 => 0
  | len + 1 => (mem (addr + .ofNat _ len)).toNat * 2 ^ (8 * len)
      + mem.read_bytesLE_asNat addr len

end Memory
end Bignum
