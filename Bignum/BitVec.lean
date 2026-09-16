/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Siddharth Bhat, Alex Keizer
-/

module

import Lean

@[expose] public section

namespace BitVec

/-!
Misc BitVec functions.
-/

/-- Set least-significant-bit at index `i` of `x` to `b`. --/
def setLsb {w : Nat} (x : BitVec w) (i : Fin w) (b : Bool) : BitVec w :=
  if b then x ||| (1#w <<< i.toNat) else x &&& ~~~(1#w <<< i.toNat)

-- theorem setLsb_getLsb {w : Nat} (x : BitVec w) (i j : Fin w) (b : Bool) :
--     (setLsb x i b).getLsb j = if i = j then b else x.getLsb j := by
--   by_cases h : i = j <;> simp [setLsb]
--   · subst i; cases b <;> simp
--   · sorry

/-!
Pattern matching over BitVec.
-/

/--
Bitvector pattern component syntax category, originally written by
Leonardo de Moura.
-/
declare_syntax_cat bvpat_comp
syntax num : bvpat_comp
syntax ident ":" num : bvpat_comp

/--
Bitvector pattern syntax category.
Example: [sf:1,0011010000,Rm:5,000000,Rn:5,Rd:5]
-/
declare_syntax_cat bvpat
syntax "[" bvpat_comp,* "]" : bvpat

open Lean

abbrev BVPatComp := TSyntax `bvpat_comp
abbrev BVPat := TSyntax `bvpat

/-- Return the number of bits in a bit-vector component pattern. -/
meta def BVPatComp.length (c : BVPatComp) : Nat := Id.run do
  match c with
  | `(bvpat_comp| $n:num) =>
    let some str := n.raw.isLit? `num | pure 0
    return str.length
  | `(bvpat_comp| $_:ident : $n:num) =>
    return n.raw.toNat
  | _ =>
    return 0

/--
If the pattern component is a bitvector literal, convert it into a bit-vector term
denoting it.
-/
meta def BVPatComp.toBVLit? (c : BVPatComp) : MacroM (Option Term) := do
  match c with
  | `(bvpat_comp| $n:num) =>
    let len := c.length
    let some str := n.raw.isLit? `num | Macro.throwErrorAt c "invalid bit-vector literal"
    let bs := str.toList
    let mut val := 0
    for b in bs do
      if b = '1' then
        val := 2*val + 1
      else if b = '0' then
        val := 2*val
      else
        Macro.throwErrorAt c "invalid bit-vector literal, '0'/'1's expected"
    let r ← `(BitVec.ofNat $(quote len) $(quote val))
    return some r
  | _ => return none

/--
If the pattern component is a pattern variable of the form `<id>:<size>` return
`some id`.
-/
meta def BVPatComp.toBVVar? (c : BVPatComp) : MacroM (Option (TSyntax `ident)) := do
  match c with
  | `(bvpat_comp| $x:ident : $_:num) =>
    return some x
  | _ => return none

meta def BVPat.getComponents (p : BVPat) : Array BVPatComp :=
  match p with
  | `(bvpat| [$comp,*]) => comp.getElems.reverse
  | _ => #[]

/--
Return the number of bits in a bit-vector pattern.
-/
meta def BVPat.length (p : BVPat) : Nat := Id.run do
  let mut sz := 0
  for c in p.getComponents do
    sz := sz + c.length
  return sz

/--
Return a term that evaluates to `true` if `var` is an instance of the pattern `pat`.
-/
meta def genBVPatMatchTest (var : Term) (pat : BVPat) : MacroM Term := do
  let mut shift := 0
  let mut result ← `(true)
  for c in pat.getComponents do
    let len := c.length
    if let some bv ← c.toBVLit? then
      let test ← `(extractLsb' $(quote shift) $(quote len) $var == $bv)
      result ← `($result && $test)
    shift := shift + len
  return result

/--
Given a variable `var` representing a term that matches the pattern `pat`, and a term `rhs`,
return a term of the form
```
let y₁ := var.extract ..
...
let yₙ := var.extract ..
rhs
```
where `yᵢ`s are the pattern variables in `pat`.
-/
meta def declBVPatVars (var : Term) (pat : BVPat) (rhs : Term) : MacroM Term := do
  let mut result := rhs
  let mut shift  := 0
  for c in pat.getComponents do
    let len := c.length
    if let some y ← c.toBVVar? then
      let rhs ← `(extractLsb' $(quote shift) $(quote len) $var)
      result ← `(let $y := $rhs; $result)
    shift := shift + len
  return result

/--
Define the `match_bv .. with | bvpat => rhs | _ => rhs`.
The last entry is the `else`-case since we currently do not check whether
the patterns are exhaustive or not.
-/
syntax "match_bv " term "with" (atomic("| " bvpat) " => " term)* ("| " "_ " " => " term) : term
macro_rules
  | `(match_bv $discr:term with
      $[ | $ps:bvpat => $rhss:term ]*
         | _ => $rhsElse:term) => do
  let mut result := rhsElse
  let x ← `(discr)
  for p in ps.reverse, rhs in rhss.reverse do
    let test ← genBVPatMatchTest x p
    let rhs ← declBVPatVars x p rhs
    result ← `(if $test then $rhs else $result)
  `(let discr := $discr; $result)

-- def test (x : BitVec 32) : BitVec 16 :=
--   match_bv x with
--   | [sf:1,0011010000,Rm:5,000000,Rn:5,Rd:5] => sf ++ Rm ++ Rn ++ Rd
--   | [sf:1,0000010000,11111000000,Rn:5,Rd:5] => sf ++ Rn ++ Rd ++ Rd
--   | _ => 0#16

-- #print test

-- def test2 (x : BitVec 4) : BitVec 4 :=
--   match_bv x with
--   | [x1:1, x2:1, x3:1, x4:1] => x4 ++ x3 ++ x2 ++ x1
--   | _ => 0#4

-- #print test2

/-- `Quote` instance for `BitVec` -/
instance (w : Nat) : Quote (BitVec w) `term where
  quote x :=
    Syntax.mkCApp ``BitVec.ofNat #[quote w, quote x.toNat]

end BitVec
