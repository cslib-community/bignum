/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/

module

@[expose] public section

/-! # More operations on bitvectors -/

set_option autoImplicit false

namespace BitVec

/--
Converts bitvector to bitstring.
-/
def toBitString {w : Nat} (x : BitVec w) : String :=
  String.ofList $ (List.range w).reverse.map (if x.getLsbD · then '1' else '0')

/--
Sets the least significant bit at index `i` of `x` to `b`.
-/
def setLsb {w : Nat} (x : BitVec w) (i : Fin w) (b : Bool) : BitVec w :=
  if b then x ||| (1#w <<< i.toNat) else x &&& ~~~(1#w <<< i.toNat)

/--
Alternative definition of `extractLsb'`.
-/
def extractLsb'Alt {w : Nat} (start len : Nat) (x: BitVec w) : BitVec len :=
  ((x / 2^start) % 2^len).setWidth len

/--
Overwrites the bits `start` to `start + len - 1` of `x` by `y` to yield a
new bitvector truncated to `x`'s size.
-/
def overwriteLsb' {w : Nat} (start len : Nat)
    (x : BitVec w) (y : BitVec len) : BitVec w :=
  (x.extractLsb' (start + len) w ++ y ++ x.extractLsb' 0 start).setWidth w

/--
Alternative definition of `overwriteLsb'`.
-/
def overwriteLsb'Alt {w : Nat} (start len : Nat)
    (x : BitVec w) (y : BitVec len) : BitVec w :=
  2^(start + len) * (x.toNat / 2^(start + len))
  + 2^start * (y.toNat % 2^len)
  + x.toNat % 2^start

end BitVec
