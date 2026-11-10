/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

import Bignum
open Bignum Bignum.Arm

/-! # Proving a simple property about `simple.S` -/

def simple : ByteList :=
  [0x22, 0x00, 0x00, 0x8b,      -- add x2, x1, x0
   0x42, 0x00, 0x01, 0xcb]      -- sub x2, x2, x1

theorem simple_spec (pc a b : BitVec 64) :
    arm.Ensures
    (fun s ↦                    -- precondition
      s.AlignedBytesLoaded pc simple ∧
      s.read PC = pc ∧
      s.read X0 = a ∧
      s.read X1 = b)
    (fun s ↦                    -- postcondition
      s.read PC = pc + 8 ∧
      s.read X2 = a)
    (MayChange [PC, X2]) := by  -- frame
  simp [Rel.Ensures]; intro s hl hPC hX0 hX1
  sorry
  --
  -- have HH := s.decode_cons (ha := hl)
  -- simp [simple, ByteList.popBitVecLE, ByteList.popLE,
  -- ByteList.toBitVecLE] at HH
  -- have HH' := HH [66#8, 0#8, 1#8, 203#8] 2332033058#32
  -- simp [Decode.decode, Decode.addOp] at HH'
  -- rcases HH' with ⟨HH'₀, HH'₁⟩
  -- --
  -- apply Rel.Eventually.step
  -- · simp [arm, hPC, HH'₀, Rel.Seq, Component.Assign, ADD]
  -- · intro s' hss'
  --   --
  --   have II := State.decode_cons (ha := HH'₁)
  --   simp [ByteList.popBitVecLE, ByteList.popLE,
  --   ByteList.toBitVecLE] at II
  --   have II' := II [] 3405840450#32
  --   simp [Decode.decode, Decode.addOp] at II'
  --   rcases II' with ⟨II'₀, _⟩
  --   --
  --   apply Rel.Eventually.step
  --   · simp [arm]
  --     sorry
  --   · sorry
