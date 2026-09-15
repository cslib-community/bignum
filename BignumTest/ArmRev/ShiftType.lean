import Bignum.ArmRev

open Bignum.ArmRev

-- LSL

/-- info: 0x00000008#32 -/
#guard_msgs in
#eval ShiftType.LSL.shift 0x4#32 1

/-- info: 0x00000000#32 -/
#guard_msgs in
#eval ShiftType.LSL.shift 0x80000000#32 1

-- LSR

/-- info: 0x00000002#32 -/
#guard_msgs in
#eval ShiftType.LSR.shift 0x4#32 1

/-- info: 0x00000000#32 -/
#guard_msgs in
#eval ShiftType.LSR.shift 0x1#32 1

-- ASR

/-- info: 0x00000000#32 -/
#guard_msgs in
#eval ShiftType.ASR.shift 0x0#32 1

/-- info: 0x00000000#32 -/
#guard_msgs in
#eval ShiftType.ASR.shift 0x1#32 1

/-- info: 0x2#4 -/
#guard_msgs in
#eval ShiftType.ASR.shift 0x5#4 1
