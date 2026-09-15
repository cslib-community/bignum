import Bignum.ArmRev

open Bignum.ArmRev

-- LSL

/-- info: 0x00000008#32 -/
#guard_msgs in
#eval ShiftType.LSL.shift 1 0x4#32

/-- info: 0x00000000#32 -/
#guard_msgs in
#eval ShiftType.LSL.shift 1 0x80000000#32

-- LSR

/-- info: 0x00000002#32 -/
#guard_msgs in
#eval ShiftType.LSR.shift 1 0x4#32

/-- info: 0x00000000#32 -/
#guard_msgs in
#eval ShiftType.LSR.shift 1 0x1#32

-- ASR

/-- info: 0x00000000#32 -/
#guard_msgs in
#eval ShiftType.ASR.shift 1 0x0#32

/-- info: 0x00000000#32 -/
#guard_msgs in
#eval ShiftType.ASR.shift 1 0x1#32

/-- info: 0x2#4 -/
#guard_msgs in
#eval ShiftType.ASR.shift 1 0x5#4

-- ROR

/-- info: 0x80#8 -/
#guard_msgs in
#eval ShiftType.ROR.shift 1 0x1#8

/-- info: 0x1#4 -/
#guard_msgs in
#eval ShiftType.ROR.shift 1 0x2#4
