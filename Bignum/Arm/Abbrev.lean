/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

public import Bignum.Arm.State

set_option linter.missingDocs false

@[expose] public section

/-! # Some handy aliases -/

namespace Bignum.Arm

abbrev X0  := XREG 0
abbrev X1  := XREG 1
abbrev X2  := XREG 2
abbrev X3  := XREG 3
abbrev X4  := XREG 4
abbrev X5  := XREG 5
abbrev X6  := XREG 6
abbrev X7  := XREG 7
abbrev X8  := XREG 8
abbrev X9  := XREG 9
abbrev X10 := XREG 10
abbrev X11 := XREG 11
abbrev X12 := XREG 12
abbrev X13 := XREG 13
abbrev X14 := XREG 14
abbrev X15 := XREG 15
abbrev X16 := XREG 16
abbrev X17 := XREG 17
abbrev X18 := XREG 18
abbrev X19 := XREG 19
abbrev X20 := XREG 20
abbrev X21 := XREG 21
abbrev X22 := XREG 22
abbrev X23 := XREG 23
abbrev X24 := XREG 24
abbrev X25 := XREG 25
abbrev X26 := XREG 26
abbrev X27 := XREG 27
abbrev X28 := XREG 28
abbrev X29 := XREG 29
abbrev X30 := XREG 30

abbrev W0  := WREG 0
abbrev W1  := WREG 1
abbrev W2  := WREG 2
abbrev W3  := WREG 3
abbrev W4  := WREG 4
abbrev W5  := WREG 5
abbrev W6  := WREG 6
abbrev W7  := WREG 7
abbrev W8  := WREG 8
abbrev W9  := WREG 9
abbrev W10 := WREG 10
abbrev W11 := WREG 11
abbrev W12 := WREG 12
abbrev W13 := WREG 13
abbrev W14 := WREG 14
abbrev W15 := WREG 15
abbrev W16 := WREG 16
abbrev W17 := WREG 17
abbrev W18 := WREG 18
abbrev W19 := WREG 19
abbrev W20 := WREG 20
abbrev W21 := WREG 21
abbrev W22 := WREG 22
abbrev W23 := WREG 23
abbrev W24 := WREG 24
abbrev W25 := WREG 25
abbrev W26 := WREG 26
abbrev W27 := WREG 27
abbrev W28 := WREG 28
abbrev W29 := WREG 29
abbrev W30 := WREG 30

abbrev Q0  := QREG 0
abbrev Q1  := QREG 1
abbrev Q2  := QREG 2
abbrev Q3  := QREG 3
abbrev Q4  := QREG 4
abbrev Q5  := QREG 5
abbrev Q6  := QREG 6
abbrev Q7  := QREG 7
abbrev Q8  := QREG 8
abbrev Q9  := QREG 9
abbrev Q10 := QREG 10
abbrev Q11 := QREG 11
abbrev Q12 := QREG 12
abbrev Q13 := QREG 13
abbrev Q14 := QREG 14
abbrev Q15 := QREG 15
abbrev Q16 := QREG 16
abbrev Q17 := QREG 17
abbrev Q18 := QREG 18
abbrev Q19 := QREG 19
abbrev Q20 := QREG 20
abbrev Q21 := QREG 21
abbrev Q22 := QREG 22
abbrev Q23 := QREG 23
abbrev Q24 := QREG 24
abbrev Q25 := QREG 25
abbrev Q26 := QREG 26
abbrev Q27 := QREG 27
abbrev Q28 := QREG 28
abbrev Q29 := QREG 29
abbrev Q30 := QREG 30
abbrev Q31 := QREG 31

abbrev D0  := DREG 0
abbrev D1  := DREG 1
abbrev D2  := DREG 2
abbrev D3  := DREG 3
abbrev D4  := DREG 4
abbrev D5  := DREG 5
abbrev D6  := DREG 6
abbrev D7  := DREG 7
abbrev D8  := DREG 8
abbrev D9  := DREG 9
abbrev D10 := DREG 10
abbrev D11 := DREG 11
abbrev D12 := DREG 12
abbrev D13 := DREG 13
abbrev D14 := DREG 14
abbrev D15 := DREG 15
abbrev D16 := DREG 16
abbrev D17 := DREG 17
abbrev D18 := DREG 18
abbrev D19 := DREG 19
abbrev D20 := DREG 20
abbrev D21 := DREG 21
abbrev D22 := DREG 22
abbrev D23 := DREG 23
abbrev D24 := DREG 24
abbrev D25 := DREG 25
abbrev D26 := DREG 26
abbrev D27 := DREG 27
abbrev D28 := DREG 28
abbrev D29 := DREG 29
abbrev D30 := DREG 30
abbrev D31 := DREG 31

end Bignum.Arm
