/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Guilherme Lima
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
  | size' + 1 => BitVec.ofNat 8 n :: ByteList.ofNatLE size' (n >>> 8)

/--
Converts an integer `n` to a little-endian byte list of `len` bytes.
Truncates the list to `len` bytes if `n` is too small or large.
-/
def ofIntLE (len : Nat) (n : Int) : ByteList :=
  ofNatLE len $ Int.natAbs (n % 256^len)

end ByteList

namespace Memory
end Memory
end Bignum
