/-
Copyright (c) 2026 Robin Arnez. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

prelude
public import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Char
import Init.Data.String.SimpEq
import Lean.Meta.StringLitProof

namespace String

open Lean Meta
open Internal.SimpEq

inductive ExprStructure where
  -- String
  | stringAppend (a b : ExprStructure)
  | push (s : ExprStructure) (c : Expr)
  | singleton (c : Expr)
  | ofList (l : ExprStructure)
  | stringLit (s : String)
  | anyString (s : Expr)
  -- List Char
  | nil
  | cons (c : Expr) (l : ExprStructure)
  | listAppend (a b : ExprStructure)
  | toList (s : ExprStructure)
  | anyList (l : Expr)

def ExprStructure.maxDepth : ExprStructure → Nat
  -- String
  | .stringAppend a b => max a.maxDepth b.maxDepth + 1
  | .push s _ => s.maxDepth + 1
  | .singleton _ => 0
  | .ofList l => l.maxDepth + 1
  | .stringLit _ => 0
  | .anyString _ => 0
  -- List Char
  | .nil => 0
  | .cons _ l => l.maxDepth + 1
  | .listAppend a b => max a.maxDepth b.maxDepth + 1
  | .toList s => s.maxDepth + 1
  | .anyList _ => 0

protected def ExprStructure.isDefEq : ExprStructure → ExprStructure → MetaM Bool
  | .stringAppend a b, .stringAppend a' b' => a.isDefEq a' <&&> b.isDefEq b'
  | .push s c, .push s' c' => s.isDefEq s' <&&> isDefEq c c'
  | .singleton c, .singleton c' => isDefEq c c'
  | .ofList l, .ofList l' => l.isDefEq l'
  | .stringLit s, .stringLit s' => pure (s == s')
  | .anyString s, .anyString s' => isDefEq s s'
  | .nil, .nil => pure true
  | .cons c l, .cons c' l' => isDefEq c c' <&&> l.isDefEq l'
  | .listAppend a b, .listAppend a' b' => a.isDefEq a' <&&> b.isDefEq b'
  | .toList s, .toList s' => s.isDefEq s'
  | .anyList l, .anyList l' => isDefEq l l'
  | _, _ => pure false

inductive CancelElement where
  | cons (l r : Expr)
  | string (e : Expr)
  | list (e : Expr)
  | char (e : Expr)

inductive Path where
  | root
  -- String
  | stringAppendLeft (parent : Path) (right : ExprStructure)
  | stringAppendRight (parent : Path) (left : ExprStructure)
  | push (parent : Path) (c : Expr)
  | toList (parent : Path)
  -- List Char
  | cons (parent : Path) (c : Expr)
  | listAppendLeft (parent : Path) (right : ExprStructure)
  | listAppendRight (parent : Path) (left : ExprStructure)
  | ofList (parent : Path)

def Path.innerLeft : Path → ExprStructure → Option (Path × ExprStructure)
  | p, .stringAppend l r => some (.stringAppendLeft p r, l)
  | p, .push s c => some (.push p c, s)
  | p, .ofList l => some (.ofList p, l)
  | _, .singleton _ | _, .stringLit _ | _, .anyString _ => none
  -- List Char
  | _, .nil | _, .cons .. => none
  | p, .listAppend l r => some (.listAppendLeft p r, l)
  | p, .toList s => some (.toList p, s)
  | _, .anyList _ => none

def Path.next : Path → ExprStructure → Path × ExprStructure
  | .root, e => (.root, e)
  -- String
  | .stringAppendLeft parent right, left => (.stringAppendRight parent left, right)
  | .stringAppendRight parent left, right => parent.next (.stringAppend left right)
  | .push parent c, s => parent.next (.push s c)
  | .toList parent, s => parent.next (.toList s)
  -- List Char
  | .cons parent c, s => parent.next (.cons c s)
  | .listAppendLeft parent right, left => (.listAppendRight parent left, right)
  | .listAppendRight parent left, right => parent.next (.listAppend left right)
  | .ofList parent, l => parent.next (.ofList l)

def Path.toStruct : Path → ExprStructure → ExprStructure
  | .root, e => e
  -- String
  | .stringAppendLeft parent right, left => parent.toStruct (.stringAppend left right)
  | .stringAppendRight parent left, right => parent.toStruct (.stringAppend left right)
  | .push parent c, s => parent.toStruct (.push s c)
  | .toList parent, s => parent.toStruct (.toList s)
  -- List Char
  | .cons parent c, s => parent.toStruct (.cons c s)
  | .listAppendLeft parent right, left => parent.toStruct (.listAppend left right)
  | .listAppendRight parent left, right => parent.toStruct (.listAppend left right)
  | .ofList parent, l => parent.toStruct (.ofList l)

def listAppendInst : Expr :=
  mkApp2 (.const ``instHAppendOfAppend [0, 0, 0]) (.app (mkConst ``List) (mkConst ``Char))
    (.app (.const ``List.instAppend [0]) (mkConst ``Char))

def stringAppendInst : Expr :=
  mkApp2 (.const ``instHAppendOfAppend [0, 0, 0]) (mkConst ``String) (mkConst ``instAppendString)

mutual

partial def createStringStructure (e : Expr) : MetaM ExprStructure := do
  if let mkStrLit s := e then
    return .stringLit s
  match_expr e with
  | String.push s c => return .push (← createStringStructure s) c
  | String.singleton c => return .singleton c
  | String.ofList l => return .ofList (← createListStructure l)
  | HAppend.hAppend _ _ _ inst a b =>
    if ← pure (inst == stringAppendInst) <||> isDefEqI inst stringAppendInst then
      return .stringAppend (← createStringStructure a) (← createStringStructure b)
    return .anyString e
  | _ => return .anyString e

partial def createListStructure (e : Expr) : MetaM ExprStructure := do
  match_expr e with
  | List.nil => return .nil
  | List.cons c l => return .cons c (← createListStructure l)
  | String.toList s => return .toList (← createStringStructure s)
  | HAppend.hAppend _ _ _ inst a b =>
    if ← pure (inst == listAppendInst) <||> isDefEqI inst listAppendInst then
      return .listAppend (← createListStructure a) (← createListStructure b)
    return .anyList e
  | _ => return .anyList e

end

public section

builtin_simproc simpEq ((_ : String) = _) := fun e => do
  unless e.isAppOfArity ``Eq 3 do return .continue
  let lhs := e.appFn!.appArg!
  let rhs := e.appArg!
  if lhs.isStringLit && rhs.isStringLit then
    return .continue -- handled in reduceEq, not here
  unless (← getEnv).contains ``StringStructure do
    return .continue -- insufficient imports
  let lhsStruct ← createStringStructure lhs
  let rhsStruct ← createStringStructure rhs
  if lhsStruct matches .anyString _ && rhsStruct matches .anyString _ then
    -- nothing to match on
    return .continue
  return .continue
