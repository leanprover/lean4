/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Basic

namespace Lean.Meta
/-!
Functions for testing whether expressions are canonical `Int` instances.
-/

def isInstOfNatInt (e : Expr) : MetaM Bool := do
  let_expr instOfNat _ ← e | return false
  return true
def isInstNegInt (e : Expr) : MetaM Bool := do
  let_expr Int.instNegInt ← e | return false
  return true
def isInstAddInt (e : Expr) : MetaM Bool := do
  let_expr Int.instAdd ← e | return false
  return true
def isInstSubInt (e : Expr) : MetaM Bool := do
  let_expr Int.instSub ← e | return false
  return true
def isInstMulInt (e : Expr) : MetaM Bool := do
  let_expr Int.instMul ← e | return false
  return true
def isInstDivInt (e : Expr) : MetaM Bool := do
  let_expr Int.instDiv ← e | return false
  return true
def isInstModInt (e : Expr) : MetaM Bool := do
  let_expr Int.instMod ← e | return false
  return true
def isInstHAddInt (e : Expr) : MetaM Bool := do
  let_expr instHAdd _ i ← e | return false
  isInstAddInt i
def isInstHSubInt (e : Expr) : MetaM Bool := do
  let_expr instHSub _ i ← e | return false
  isInstSubInt i
def isInstHMulInt (e : Expr) : MetaM Bool := do
  let_expr instHMul _ i ← e | return false
  isInstMulInt i
def isInstHDivInt (e : Expr) : MetaM Bool := do
  let_expr instHDiv _ i ← e | return false
  isInstDivInt i
def isInstHModInt (e : Expr) : MetaM Bool := do
  let_expr instHMod _ i ← e | return false
  isInstModInt i
def isInstLTInt (e : Expr) : MetaM Bool := do
  let_expr Int.instLTInt ← e | return false
  return true
def isInstLEInt (e : Expr) : MetaM Bool := do
  let_expr Int.instLEInt ← e | return false
  return true

end Lean.Meta
