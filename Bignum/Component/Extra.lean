/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Guilherme Lima
-/
module

public import Bignum.BitVec
public import Bignum.Component.Basic

@[expose] public section

/-! # More components -/

set_option autoImplicit false

namespace Bignum.Component

/--
Component for a bit within a bitvector.
-/
def bitelement {w : Nat} (i : Fin w) : Component (BitVec w) Bool :=
  ⟨λ bv ↦ bv.getLsb i, λ b bv ↦ BitVec.setLsb bv i b⟩

/--
Component for subwords of a bitvector.
-/
def subword {w : Nat} (start len : Nat) :
    Component (BitVec w) (BitVec len) :=
  ⟨BitVec.extractLsb' start len, λ b bv ↦ bv.overwriteLsb' start len b⟩

/--
Component for the bottom-half of a bitvector.
-/
def bottomhalf {w : Nat} : Component (BitVec w) (BitVec (w / 2)) :=
  subword 0 (w / 2)

/--
Component for the top-half of a bitvector.
-/
def tophalf {w : Nat} : Component (BitVec w) (BitVec (w.succ / 2)) :=
  subword (w / 2) (w.succ / 2)

/-
Components for subwords of bitvectors with a specific length.
-/
def bottom_256 : Component (BitVec 512) (BitVec 256) := @bottomhalf 512
def top_256    : Component (BitVec 512) (BitVec 256) := @tophalf 512
def bottom_128 : Component (BitVec 256) (BitVec 128) := @bottomhalf 256
def top_128    : Component (BitVec 256) (BitVec 128) := @tophalf 256
def bottom_64  : Component (BitVec 128) (BitVec 64)  := @bottomhalf 128
def top_64     : Component (BitVec 128) (BitVec 64)  := @tophalf 128
def bottom_32  : Component (BitVec 64) (BitVec 32)   := @bottomhalf 64
def top_32     : Component (BitVec 64) (BitVec 32)   := @tophalf 64
def bottom_16  : Component (BitVec 32) (BitVec 16)   := @bottomhalf 32
def top_16     : Component (BitVec 32) (BitVec 16)   := @tophalf 32
def bottom_8   : Component (BitVec 16) (BitVec 8)    := @bottomhalf 16
def top_8      : Component (BitVec 16) (BitVec 8)    := @tophalf 16

/-
Components for subwords of larger bitvectors which force a zero
extension on writes.  Intended to mimic x86-64 and aarch64 behaviors.
-/
def zerotop_256 : Component (BitVec 512) (BitVec 256) :=
  Component.through (BitVec.truncate 256) (BitVec.truncate 512)

def zerotop_128 : Component (BitVec 256) (BitVec 128) :=
  Component.through (BitVec.truncate 128) (BitVec.truncate 256)

def zerotop_64 : Component (BitVec 128) (BitVec 64) :=
  Component.through (BitVec.truncate 64) (BitVec.truncate 128)

def zerotop_32 : Component (BitVec 64) (BitVec 32) :=
  Component.through (BitVec.truncate 32) (BitVec.truncate 64)

def zerotop_8 : Component (BitVec 16) (BitVec 8) :=
  Component.through (BitVec.truncate 8) (BitVec.truncate 16)

end Bignum.Component
