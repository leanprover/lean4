/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Basic

namespace Lean.Meta
/-!
Functions for testing whether expressions are canonical `Nat` instances.
-/

def isInstOfNatNat (e : Expr) : MetaM Bool := do
  let_expr instOfNatNat _ ← e | return false
  return true
def isInstAddNat (e : Expr) : MetaM Bool := do
  let_expr instAddNat ← e | return false
  return true
def isInstSubNat (e : Expr) : MetaM Bool := do
  let_expr instSubNat ← e | return false
  return true
def isInstMulNat (e : Expr) : MetaM Bool := do
  let_expr instMulNat ← e | return false
  return true
def isInstDivNat (e : Expr) : MetaM Bool := do
  let_expr Nat.instDiv ← e | return false
  return true
def isInstModNat (e : Expr) : MetaM Bool := do
  let_expr Nat.instMod ← e | return false
  return true
def isInstNatPowNat (e : Expr) : MetaM Bool := do
  let_expr instNatPowNat ← e | return false
  return true
def isInstPowNat (e : Expr) : MetaM Bool := do
  let_expr instPowNat _ i ← e | return false
  isInstNatPowNat i
def isInstHAddNat (e : Expr) : MetaM Bool := do
  let_expr instHAdd _ i ← e | return false
  isInstAddNat i
def isInstHSubNat (e : Expr) : MetaM Bool := do
  let_expr instHSub _ i ← e | return false
  isInstSubNat i
def isInstHMulNat (e : Expr) : MetaM Bool := do
  let_expr instHMul _ i ← e | return false
  isInstMulNat i
def isInstHDivNat (e : Expr) : MetaM Bool := do
  let_expr instHDiv _ i ← e | return false
  isInstDivNat i
def isInstHModNat (e : Expr) : MetaM Bool := do
  let_expr instHMod _ i ← e | return false
  isInstModNat i
def isInstHPowNat (e : Expr) : MetaM Bool := do
  let_expr instHPow _ _ i ← e | return false
  isInstPowNat i
def isInstLTNat (e : Expr) : MetaM Bool := do
  let_expr instLTNat ← e | return false
  return true
def isInstLENat (e : Expr) : MetaM Bool := do
  let_expr instLENat ← e | return false
  return true
def isInstDvdNat (e : Expr) : MetaM Bool := do
  let_expr Nat.instDvd ← e | return false
  return true

end Lean.Meta
