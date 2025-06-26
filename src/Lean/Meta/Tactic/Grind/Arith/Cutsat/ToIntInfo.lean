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

structure ToIntCongr where
  c?    : Option Expr := none
  c_ww? : Option Expr := none
  c_wl? : Option Expr := none
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
  add       : ToIntCongr
  mul       : ToIntCongr
  -- TODO: other operators

end Lean.Meta.Grind.Arith.Cutsat
