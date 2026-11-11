/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Bignum.Arm.Arm
public import Bignum.Arm.StateLemmas

@[expose] public section

/-! # Theorems about ARM semantics -/

namespace Bignum.Arm
namespace State

variable (s : State) (addr : BitVec 64) (bs bs' : ByteList)

/-! ## Instruction decoding -/

theorem decode_eq_none_iff : s.decode addr = none ↔ ¬ 4 ∣ addr.toNat ∨
    Decode.decode (s.fetch addr) = none := by
  grind [decode]

theorem decode_eq_some_iff (data : BitVec 32) (instr : Rel State State) :
    s.decode addr = some (data, instr) ↔
    s.AlignedBytesLoaded addr (.ofBitVecLE 4 data) ∧
    Decode.decode (s.fetch addr) = some instr := by
  constructor
  · simp [decode]; intro h4 h
    constructor <;> split at h <;> injections <;> try contradiction
    · refine ⟨h4, ?_⟩; subst data; unfold Memory.BytesLoadedLE
      rw [ByteList.length_ofBitVecLE, ← read_bytes, fetch]
      exact (ByteList.ofBitVecLE_toBitVecLE_of_length_eq _
        (length_read_bytes s addr 4) _).symm
    · subst instr; assumption
  · intro ⟨ha, hd⟩; simp [decode, ha.aligned, hd]
    have h : s.read (bytes addr 4) = ByteList.ofBitVecLE 4 data := by
      rw [read_bytes]
      exact (Memory.BytesLoadedLE_ofBitVecLE_iff _ _ _ _).mp ha.bytesLoadedLE
    exact ByteList.ofBitVecLE_inj _ _ rfl
      ((ByteList.ofBitVecLE_toBitVecLE_of_length_eq _
        (length_read_bytes s addr 4) (by rw [length_read_bytes])).trans h)

-- theorem decode_def (s : State) (addr: BitVec 64) (instr : Rel State State) :
--     s.Decode addr instr ↔
--     ∃ data, s.decode addr = some (data, instr) ∧
--       s.AlignedBytesLoaded addr (.ofBitVecLE 4 data) := by
--   constructor
--   · sorry
--   · sorry

-- theorem decode_cons (bs bs' : ByteList)
--     (data : BitVec 32) (instr : Rel State State)
--     (ha : s.AlignedBytesLoaded addr bs)
--     (hpop : bs.popBitVecLE 4 = some (data, bs'))
--     (hdec : Decode.decode data = .some instr) :
--     s.decode addr = some instr ∧ s.AlignedBytesLoaded (addr + 4#64) bs' := by
--   rcases (bs.popBitVecLE_eq_some_iff _ _ _).mp hpop with ⟨hn, hl, hr⟩
--   have h4 : (bs.take 4).length = 4 := by
--     rw [List.length_take, Nat.min_eq_left]; assumption
--   have h4dvd : 4 ∣ (bs.take 4).length := by
--     rw [h4]; apply Nat.dvd_refl
--   constructor
--   · simp [ha.aligned, decode_eq_some_iff]
--     have hb := (((s.read memory).BytesLoadedLE_append addr (bs.take 4)
--       (bs.drop 4)).mp (by
--       rw [bs.take_append_drop]; exact ha.bytesLoadedLE)).left
--     unfold Memory.BytesLoadedLE at hb
--     rw [h4] at hb
--     have hx : s.read (bytes addr 4) = bs.take 4 := hb
--     have e : (s.read (bytes addr 4)).toBitVecLE = data := by
--       apply BitVec.eq_of_toNat_eq
--       have h1 : ByteList.toNatLE (bs.take 4) = data.toNat := by
--         have := congrArg BitVec.toNat hl
--         rw [ByteList.toBitVecLE_toNat, BitVec.toNat_cast] at this
--         exact this
--       have h2 : ByteList.toNatLE (s.read (bytes addr 4)) =
--           ByteList.toNatLE (bs.take 4) :=
--         congrArg ByteList.toNatLE hx
--       rw [ByteList.toBitVecLE_toNat]
--       exact h2.trans h1
--     rw [e]; exact hdec
--   · constructor
--     · grind [ha.aligned]
--     · have X := (s.read memory).AlignedBytesLoadedLE_append'
--         addr (bs.take 4) (bs.drop 4) h4dvd
--       rw [bs.take_append_drop] at X
--       have Y := (X.mp ha).right
--       rw [h4] at Y
--       rw [← hr]
--       apply Y.bytesLoadedLE


end State
end Bignum.Arm
