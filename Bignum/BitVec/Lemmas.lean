/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/

module

public import Bignum.BitVec.Basic

@[expose] public section

/-! # More theorems about bitvectors -/

set_option autoImplicit false

namespace BitVec

theorem setLsb_getLsb {w : Nat} (x : BitVec w) (i j : Fin w) (b : Bool) :
    (x.setLsb i b).getLsb j = if i = j then b else x.getLsb j := by
  unfold setLsb; cases b <;> by_cases h : i = j <;>
  simp [h] <;> rcases Fin.lt_or_lt_of_ne h <;> lia

theorem overwriteLsb'_extractLsb'_low {w : Nat} (start len : Nat)
    (x : BitVec w) (y : BitVec len) :
    (x.overwriteLsb' start len y).extractLsb' 0 start
    = x.extractLsb' 0 start := by
  rw [overwriteLsb', setWidth_append, setWidth_append]; grind
  -- by_cases h₁ : w ≤ start
  -- · rw [dif_pos h₁, setWidth_extractLsb'_of_le h₁, extractLsb'_eq_self]
  -- · rw [dif_neg h₁]
  --   by_cases h₂ : w ≤ len + start <;> simp
  --   · rw [dif_pos h₂]
  --     grind
  --   · grind

theorem overwriteLsb'_extractLsb'_high {w : Nat} (start len : Nat)
    (x : BitVec w) (y : BitVec len) :
    (x.overwriteLsb' start len y).extractLsb' (start + len) w
    = x.extractLsb' (start + len) w := by
  rw [overwriteLsb', setWidth_append, setWidth_append]; grind

-- theorem overwriteLsb'_extractLsb'_mid {w : Nat} (start len : Nat)
--     (x : BitVec w) (y : BitVec len) :
--     (x.overwriteLsb' start len y).extractLsb' start len
--     = sorry := by
--   sorry

end BitVec
