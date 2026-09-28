/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Guilherme Lima
-/
module

public import Bignum.Component

@[expose] public section

/-! # Byte-addressable memory -/

set_option autoImplicit false

/-! ## Byte list -/

abbrev ByteList := List (BitVec 8)

namespace ByteList

/--
Converts a little-endian byte list `bs` to a natural number.
-/
def toNatLE (bs : ByteList) : Nat :=
  bs.foldr (λ b n ↦ b.toNat + n <<< 8) 0

/--
Converts a natural number `n` to a little-endian byte list of `size` bytes.
Truncates the list if `n` is too large.
-/
def ofNatLE (size n : Nat) : ByteList :=
  match size with
  | 0 => []
  | size' + 1 => n :: ByteList.ofNatLE size' (n >>> 8)

/--
Converts an integer `n` to a little-endian byte list of `size` bytes.
Truncates the list to `size` bytes if `n` is too small or large.
-/
def ofIntLE (size : Nat) (n : Int) : ByteList :=
  ofNatLE size $ Int.toNat (n.emod (256 ^ size))

end ByteList

namespace Bignum.Memory
end Bignum.Memory
