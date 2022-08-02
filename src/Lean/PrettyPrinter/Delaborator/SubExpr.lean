/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Daniel Selsam, Wojciech Nawrocki
-/
import Lean.Meta.Basic
import Lean.SubExpr
import Std.Data.RBMap

/-!
# Subexpr utilities for delaborator.
This file defines utilities for `MetaM` computations to traverse subexpressions of an expression
in sync with the `Nat` "position" values that refer to them.
-/

namespace Lean.PrettyPrinter.Delaborator

abbrev OptionsPerPos := Std.RBMap SubExpr.Pos Options compare

namespace SubExpr

open Lean.SubExpr

variable {α : Type} [Inhabited α]
variable {m : Type → Type} [Monad m]

section Descend

variable [MonadReaderOf SubExpr m] [MonadWithReaderOf SubExpr m]
variable [MonadLiftT MetaM m] [MonadControlT MetaM m]
variable [MonadLiftT IO m]

def getExpr : m Expr := return (← readThe SubExpr).expr
def getPos  : m Pos  := return (← readThe SubExpr).pos

def descend (child : Expr) (childIdx : Nat) (x : m α) : m α :=
  withTheReader SubExpr (fun cfg => { cfg with expr := child, pos := cfg.pos.push childIdx }) x

def withAppFn   (x : m α) : m α := do descend (← getExpr).appFn!  0 x
def withAppArg  (x : m α) : m α := do descend (← getExpr).appArg! 1 x

def withType (x : m α) : m α := do
  descend (← Meta.inferType (← getExpr)) Pos.typeCoord x -- phantom positions for types

partial def withAppFnArgs (xf : m α) (xa : α → m α) : m α := do
  if (← getExpr).isApp then
    let acc ← withAppFn (withAppFnArgs xf xa)
    withAppArg (xa acc)
  else xf

def withBindingDomain (x : m α) : m α := do descend (← getExpr).bindingDomain! 0 x

def withBindingBody (n : Name) (x : m α) : m α := do
  let e ← getExpr
  Meta.withLocalDecl n e.binderInfo e.bindingDomain! fun fvar =>
    descend (e.bindingBody!.instantiate1 fvar) 1 x

def withProj (x : m α) : m α := do
  let Expr.proj _ _ e ← getExpr | unreachable!
  descend e 0 x

def withMDataExpr (x : m α) : m α := do
  let Expr.mdata _ e ← getExpr | unreachable!
  withTheReader SubExpr (fun ctx => { ctx with expr := e }) x

def withLetVarType (x : m α) : m α := do
  let Expr.letE _ t _ _ _ ← getExpr | unreachable!
  descend t 0 x

def withLetValue (x : m α) : m α := do
  let Expr.letE _ _ v _ _ ← getExpr | unreachable!
  descend v 1 x

def withLetBody (x : m α) : m α := do
  let Expr.letE n t v b _ ← getExpr | unreachable!
  Meta.withLetDecl n t v fun fvar =>
    let b := b.instantiate1 fvar
    descend b 2 x

def withNaryFn (x : m α) : m α := do
  let e ← getExpr
  let newPos := (← getPos).pushNaryFn e.getAppNumArgs
  withTheReader SubExpr (fun cfg => { cfg with expr := e.getAppFn, pos := newPos }) x

def withNaryArg (argIdx : Nat) (x : m α) : m α := do
  let e ← getExpr
  let args := e.getAppArgs
  let newPos := (← getPos).pushNaryArg args.size argIdx
  withTheReader SubExpr (fun cfg => { cfg with expr := args[argIdx]!, pos := newPos }) x

end Descend

structure HoleIterator where
  curr : Nat := 2
  top  : Nat := Pos.maxChildren
  deriving Inhabited

section Hole

variable {α : Type} [Inhabited α]
variable {m : Type → Type} [Monad m]
variable [MonadStateOf HoleIterator m]

def HoleIterator.toPos (iter : HoleIterator) : Pos :=
  iter.curr

def HoleIterator.next (iter : HoleIterator) : HoleIterator :=
  if (iter.curr+1) == iter.top then
    ⟨2*iter.top, Pos.maxChildren*iter.top⟩
  else ⟨iter.curr+1, iter.top⟩

/-- The positioning scheme guarantees that there will be an infinite number of extra positions
which are never used by `Expr`s. The `HoleIterator` always points at the next such "hole".
We use these to attach additional `Elab.Info`. -/
def nextExtraPos : m Pos := do
  let iter ← getThe HoleIterator
  let pos := iter.toPos
  modifyThe HoleIterator HoleIterator.next
  return pos

end Hole
end SubExpr

end Lean.PrettyPrinter.Delaborator
