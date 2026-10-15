/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

import Bignum.Memory
open Bignum

/-! # Unit test for memory operations -/

/-! ## Byte list -/

def bs : ByteList := [0xef, 0xcd, 0xab, 0x00]
example : ByteList.ofNatLE 4 bs.toNatLE = bs := by rfl
example : ByteList.ofNatLE 6 bs.toNatLE = bs ++ [0, 0] := by rfl
example : ByteList.ofIntLE 2 (-129) = [0x7f, 0xff] := by rfl
example : ByteList.ofIntLE 1 (-129) = [0x7f] := by rfl

/-! ## Memory -/

def mem : Memory 64 := BitVec.truncate 8

/-! ### readBytesLE -/

example : mem.readBytesLE 0 4 = [0x00#8, 0x01#8, 0x02#8, 0x03#8] := by rfl
example : mem.readBytesNatLE 0 4 = 0x03020100 := by rfl
example : mem.readBytesNatLE 0 4 = 50462976 := by rfl

example : (mem.readBytesLE 0 4).toNatLE =
    mem.readBytesNatLE 0 4 := by rfl
example : (mem.readBytesLE 8 13).toNatLE =
    mem.readBytesNatLE 8 13 := by rfl

-- wraps around and starts reading from the beginning of the address space
example : mem.readBytesLE (BitVec.allOnes 64) 3
    = [0xff#8, 0x00#8, 0x01#8] := by rfl
example: mem.readBytesNatLE (BitVec.allOnes 64) 3
    = 65791 := by rfl

/-! ### writeBytesLE -/

example : (mem.writeBytesLE 2 2 [0xaa, 0xbb]).readBytesLE 2 4 =
    [0xaa#8, 0xbb#8, 0x04#8, 0x05#8] := by rfl

example : (mem.writeBytesLE 2 2 [0xaa, 0xbb]).readBytesLE 2 4 =
    (mem.writeBytesNatLE' 2 2 48042).readBytesLE 2 4 := by rfl

-- wraps around and starts writing to the beginning of the address space
example : (mem.writeBytesNatLE'
    (.allOnes 64) 3 0x010203).readBytesLE (.allOnes 64) 3 =
    [0x03, 0x02, 0x01] := by rfl

example : (mem.writeBytesNatLE
    (.allOnes 64) 3 0x010203).readBytesLE (.allOnes 64) 3 =
    [0x03, 0x02, 0x01] := by rfl

/-! ### BytesLoadedLE -/

example : (.allZeros : Memory 64).BytesLoadedLE 0#64 [0#8,0#8] := by decide
example : (.allOnes : Memory 64).BytesLoadedLE
    0#64 [0xff#8,0xff#8] := by decide

/-! ### AlignedBytesLoadedLE -/

example : (.allZeros : Memory 64).AlignedBytesLoadedLE
    0#64 [0#8,0#8] := by decide
example : (.allZeros : Memory 64).AlignedBytesLoadedLE
    4#64 [0#8,0#8] := by decide
example : ¬(.allZeros : Memory 64).AlignedBytesLoadedLE
    6#64 [0#8,0#8] := by decide
