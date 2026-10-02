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
example : mem.read_bytesLE 0 4 = [0x00#8, 0x01#8, 0x02#8, 0x03#8] := by rfl
example : mem.read_bytesLE_asNat 0 4 = 0x03020100 := by rfl
example : (mem.read_bytesLE 0 4).toNatLE
  = mem.read_bytesLE_asNat 0 4 := by rfl
example : (mem.read_bytesLE 8 13).toNatLE
  = mem.read_bytesLE_asNat 8 13 := by rfl

example : (mem.write_bytesLE 2 2 [0xaa, 0xbb]).read_bytesLE 2 4
    = [0xaa#8, 0xbb#8, 0x04#8, 0x05#8] := by rfl
example : (mem.write_bytesLE 2 2 [0xaa, 0xbb]).read_bytesLE 2 4
    = (mem.write_bytesLE_asNat 2 2 48042).read_bytesLE 2 4 := by rfl
