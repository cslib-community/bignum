/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Bignum.BitVec
public import Bignum.Component.Basic
public import Bignum.Memory

@[expose] public section

/-! # More components -/

namespace Bignum.Component

universe u v

/-! ## General -/

/--
Pseudo-component for reading a value (write is no-op).
-/
def rvalue {α : Type u} {β : Type v} (b : β) : Component α β :=
  ⟨fun _ ↦ b, fun _ a ↦ a⟩

/--
Component for a function with a BEq domain.
-/
def element {α : Type u} [BEq α] {β : Type v} (a : α)
    : Component (α → β) β :=
  ⟨fun f ↦ f a, fun b f a' ↦ if a' == a then b else f a'⟩

/--
Component for applying a pair of functions (f,g) to a component.
-/
def through {α : Type u} {β : Type v} (f : α → β) (g : β → α)
    : Component α β :=
  ⟨f, fun b _ ↦ g b⟩

/-! ## Bitvector -/

/--
A bit within a bitvector.
-/
def bitelement {w : Nat} (i : Fin w) : Component (BitVec w) Bool :=
  ⟨fun bv ↦ bv.getLsb i, fun b bv ↦ bv.setLsb i b⟩

/--
A subword of a bitvector.
-/
def subword {w : Nat} (start len : Nat) :
    Component (BitVec w) (BitVec len) :=
  ⟨.extractLsb' start len, fun b bv ↦ bv.overwriteLsb' start len b⟩

/--
The bottom-half of a bitvector.
-/
def bottomhalf {w : Nat} : Component (BitVec w) (BitVec (w / 2)) :=
  subword 0 (w / 2)

/--
The top-half of a bitvector.
-/
def tophalf {w : Nat} : Component (BitVec w) (BitVec (w.succ / 2)) :=
  subword (w / 2) (w.succ / 2)

/--
The bottom 256 bits of a 512-bit bitvector.
-/
def bottom256 : Component (BitVec 512) (BitVec 256) :=
  bottomhalf

/--
The bottom 128 bits of a 256-bit bitvector.
-/
def bottom128 : Component (BitVec 256) (BitVec 128) :=
  bottomhalf

/--
The bottom 64 bits of a 128-bit bitvector.
-/
def bottom64 : Component (BitVec 128) (BitVec 64) :=
  bottomhalf

/--
The bottom 32 bits of a 64-bit bitvector.
-/
def bottom32 : Component (BitVec 64) (BitVec 32) :=
  bottomhalf

/--
The bottom 16 bits of a 32-bit bitvector.
-/
def bottom16 : Component (BitVec 32) (BitVec 16) :=
  bottomhalf

/--
The bottom 8 bits of a 16-bit bitvector.
-/
def bottom8 : Component (BitVec 16) (BitVec 8) :=
  bottomhalf

/--
The top 256 bits of a 512-bit bitvector.
-/
def top256 : Component (BitVec 512) (BitVec 256) :=
  tophalf

/--
The top 128 bits of a 256-bit bitvector.
-/
def top128 : Component (BitVec 256) (BitVec 128) :=
  tophalf

/--
The top 64 bits of a 128-bit bitvector.
-/
def top64 : Component (BitVec 128) (BitVec 64) :=
  tophalf

/--
The top 32 bits of a 64-bit bitvector.
-/
def top32 : Component (BitVec 64) (BitVec 32) :=
  tophalf

/--
The top 16 bits of a 32-bit bitvector.
-/
def top16 : Component (BitVec 32) (BitVec 16) :=
  tophalf

/--
The top 8 bits of a 16-bit bitvector.
-/
def top8 : Component (BitVec 16) (BitVec 8) :=
  tophalf

/--
The bottom 256 bits of 512-bit bitvector, zeroing the top 256 bits on write.
-/
def zerotop256 : Component (BitVec 512) (BitVec 256) :=
  .through (.truncate 256) (.truncate 512)

/--
The bottom 128 bits of 256-bit bitvector, zeroing the top 128 bits on write.
-/
def zerotop128 : Component (BitVec 256) (BitVec 128) :=
  .through (.truncate 128) (.truncate 256)

/--
The bottom 64 bits of 128-bit bitvector, zeroing the top 64 bits on write.
-/
def zerotop64 : Component (BitVec 128) (BitVec 64) :=
  .through (.truncate 64) (.truncate 128)

/--
The bottom 32 bits of 64-bit bitvector, zeroing the top 32 bits on write.
-/
def zerotop32 : Component (BitVec 64) (BitVec 32) :=
  .through (.truncate 32) (.truncate 64)

/--
The bottom 16 bits of 32-bit bitvector, zeroing the top 16 bits on write.
-/
def zerotop16 : Component (BitVec 32) (BitVec 16) :=
  .through (.truncate 16) (.truncate 32)

/--
The bottom 8 bits of 16-bit bitvector, zeroing the top 8 bits on write.
-/
def zerotop8 : Component (BitVec 16) (BitVec 8) :=
  .through (.truncate 8) (.truncate 16)

/-! ## Memory -/

/--
Component for a multi-byte chunk of memory in little-endian encoding.  The
chunk is represented as a byte list.  `addr` is the address from (to) which
the chunk should be read (written).  `len` is the size of the chunk in
bytes.
-/
def bytesLE {w : Nat} (addr : BitVec w) (len : Nat) :
    Component (Memory w) ByteList :=
  ⟨fun mem ↦ Memory.readBytesLE mem addr len,
   fun bs mem ↦ Memory.writeBytesLE mem addr len bs⟩

end Bignum.Component
