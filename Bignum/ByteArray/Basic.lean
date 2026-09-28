/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/

module

@[expose] public section

/-! # More operations on byte arrays -/

set_option autoImplicit false

/-
The "LE" suffix means little-endian.  Recall that in the little-endian
representation the least significant byte is stored at the lowest position.
So, the 32-bit integer `0x00abcdef` is represented by the 4-byte array
`[0xef,0xcd,0xab,0x00]`.
-/

namespace ByteArray

/--
Converts a little-endian byte array `bs` to a natural number.
-/
def toNatLE (bs : ByteArray) : Nat :=
  bs.foldl (· + UInt8.toNat · <<< 8) 0

def toNatLE_Alt (bs : ByteArray) : Nat :=
  let rec @[implicit_reducible] loop
    | [] => 0
    | b :: l' => b.toNat + loop l' <<< 8
  loop bs.toList

/--
Converts a natural number `n` to a little-endian byte array of `size` bytes.
Truncates the array to `size` bytes if `n` is too large.
-/
def ofNatLE (size n : Nat) : ByteArray :=
  match size with
  | 0 => ByteArray.emptyWithCapacity size
  | size' + 1 => (ofNatLE size' n).push (UInt8.ofNat (n >>> (size' * 8)))

def ofNatLE_Alt (size n : Nat) : ByteArray :=
  let rec @[implicit_reducible] loop
    | 0, _ => []
    | sz + 1, m => UInt8.ofNat m :: loop sz (m >>> 8)
  List.toByteArray $ loop size n

/--
Converts an integer `n` to a little-endian byte array of `size` bytes.
Truncates the array to `size` bytes if `n` is too large or too small.
-/
def ofIntLE (size : Nat) (n : Int) : ByteArray :=
  ofNatLE size $ Int.toNat (n.emod (256^size))

end ByteArray
