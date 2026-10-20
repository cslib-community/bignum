/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

import Bignum.Component.Extra
open Bignum.Component

set_option exponentiation.threshold 512

/-! # Unit test for extra components -/

def f512 : BitVec 512 := .allOnes 512
def f256 : BitVec 256 := .allOnes 256
def f128 : BitVec 128 := .allOnes 128
def f64  : BitVec 64  := .allOnes 64
def f32  : BitVec 32  := .allOnes 32
def f16  : BitVec 16  := .allOnes 16
def f8   : BitVec 8   := .allOnes 8

def z512 : BitVec 512 := 0
def z256 : BitVec 256 := 0
def z128 : BitVec 128 := 0
def z64  : BitVec 64  := 0
def z32  : BitVec 32  := 0
def z16  : BitVec 16  := 0
def z8   : BitVec 8   := 0

/-! ## bitelement -/

namespace bitelement_NS
def bv : BitVec 8 := 0b01001011#8
example : (bitelement 0).read bv = true := by rfl
example : (bitelement 1).read bv = true := by rfl
example : (bitelement 2).read bv = false := by rfl
example : (bitelement 3).read bv = true := by rfl
example : (bitelement 3).write false bv = 0b01000011#8 := by rfl
namespace bitelement_NS

/-! ## subword, bottomhalf, tophalf -/

namespace subword_NS
def bv : BitVec 8 := 0b01001011#8
example : (subword 0 3).read bv = 0b11#3 := by rfl
example : (subword 4 1).read bv = 0#1 := by rfl
example : (subword 0 0).read bv = 0#0 := by rfl
example : (subword 6 3).read bv = 1#3 := by rfl
example : (subword 7 3).read bv = 0#3 := by rfl
example : (subword 100 2).read bv = 0#2 := by rfl
example : (subword 0 3).write 0 bv = 0b01001000#8 := by rfl
example : (subword 1 3).write 0b101 bv = 0b01001011#8 := by rfl
example : (subword 6 4).write 0xf bv = 0b11001011#8 := by rfl
example : bottomhalf.read bv = 0b1011#4 := by rfl
example : bottomhalf.read 0b11#2 = 0b1#1 := by rfl
example : bottomhalf.read 0b11#0 = 0b1#0 := by rfl
example : bottomhalf.write 0xf bv = 0b01001111#8 := by rfl
example : bottomhalf.write 0xf 0#2 = 1#2 := by rfl
example : bottomhalf.write 0xf 0#0 = 0#0 := by rfl
example : tophalf.read bv = 0b0100#4 := by rfl
example : tophalf.read 0b11#2 = 0b1#1 := by rfl
example : tophalf.read 0b11#0 = 0b1#0 := by rfl
example : tophalf.write 0xf bv = 0b11111011#8 := by rfl
example : tophalf.write 0xf 0#2 = 2#2 := by rfl
example : tophalf.write 0xf 0#0 = 0#0 := by rfl
example : tophalf.write 0x0 111#3 = 0b001#3 := by rfl
end subword_NS

/-! ## bottom*, top* -/

namespace bottomtopNS
example : bottom256.read f512 = f256 := by rfl
example : bottom128.read f256 = f128 := by rfl
example : bottom64.read f128 = f64 := by rfl
example : bottom32.read f64 = f32 := by rfl
example : bottom16.read f32 = f16 := by rfl
example : bottom8.read f16 = f8 := by rfl
example : top256.read f512 = f256 := by rfl
example : top128.read f256 = f128 := by rfl
example : top64.read f128 = f64 := by rfl
example : top32.read f64 = f32 := by rfl
example : top16.read f32 = f16 := by rfl
example : top8.read f16 = f8 := by rfl
end bottomtopNS

/-! ## zerotop* -/

namespace zerotopNS
example : zerotop256.read f512 = f256 := by rfl
example : zerotop256.write f256 f512 = z256 ++ f256 := by rfl
example : zerotop128.read f256 = f128 := by rfl
example : zerotop128.write f128 f256 = z128 ++ f128 := by rfl
example : zerotop64.read f128 = f64 := by rfl
example : zerotop64.write f64 f128 = z64 ++ f64 := by rfl
example : zerotop32.read f64 = f32 := by rfl
example : zerotop32.write f32 f64 = z32 ++ f32 := by rfl
example : zerotop16.read f32 = f16 := by rfl
example : zerotop16.write f16 f32 = z16 ++ f16 := by rfl
example : zerotop8.read f16 = f8 := by rfl
example : zerotop8.write f8 f16 = z8 ++ f8 := by rfl
example : zerotop8.write 0xff 0x1000 = 0x00ff := by rfl
end zerotopNS
