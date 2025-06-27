/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.ToInt
import Lean.Meta.Tactic.Grind.Arith.Util

namespace Lean.Meta.Grind.Arith.Cutsat
open Lean Grind

/--
Theorems for operators that have support for `i.wrap` over `i.wrap` simplification.
Currently only addition and multiplication have `wrap` cancellation theorems
-/
structure ToIntThms where
  /--
  Basic theorem of the form
  ```
  toInt a = a' → toInt b = b' → toInt (a ⊞ b) = i.wrap (a' ⊞ b')`
  ```
  -/
  c?    : Option Expr := none
  /--
  Left-right `wrap` cancellation theorem of the form
  ```
  toInt a = i.wrap a' → toInt b = i.wrap b' → toInt (a ⊞ b) = i.wrap (a' ⊞ b')
  ```
  -/
  c_ww? : Option Expr := none
  /--
  Left `wrap` cancellation theorem of the form
  ```
  toInt a = i.wrap a' → toInt b = b' → toInt (a ⊞ b) = i.wrap (a' ⊞ b')
  ```
  -/
  c_wl? : Option Expr := none
  /--
  Right `wrap` cancellation theorem of the form
  ```
  toInt a = a' → toInt b = i.wrap b' → toInt (a ⊞ b) = i.wrap (a' ⊞ b')
  ```
  -/
  c_wr? : Option Expr := none

structure ToIntInfo where
  type      : Expr
  u         : Level
  toIntInst : Expr
  rangeExpr : Expr
  range     : IntInterval
  toInt     : Expr
  wrap      : Expr
  -- theorem `of_eq_wrap_co_0` if `range == .co 0 hi`
  ofWrap0?  : Option Expr
  ofEq      : Expr
  ofDiseq   : Expr
  ofLE?     : Option Expr
  ofNotLE?  : Option Expr
  ofLT?     : Option Expr
  ofNotLT?  : Option Expr
  addThms   : ToIntThms
  mulThms   : ToIntThms
  subThm?   : Option Expr
  negThm?   : Option Expr
  divThm?   : Option Expr
  modThm?   : Option Expr
  powThm?   : Option Expr
  zeroThm?  : Option Expr
  ofNatThm? : Option Expr
  lowerThm? : Option Expr
  upperThm? : Option Expr

/--
For each term `e` of type `α` which implements the `ToInt α i` class,
we store its corresponding `Int` term `eToInt`, a proof `he : toInt e = eToInt`,
and the type `α`.
-/
structure ToIntTermInfo where
  eToInt : Expr
  α      : Expr
  he     : Expr

end Lean.Meta.Grind.Arith.Cutsat
