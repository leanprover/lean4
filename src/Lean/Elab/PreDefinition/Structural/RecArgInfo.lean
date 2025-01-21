/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
prelude
import Lean.Meta.Basic
import Lean.Meta.ForEachExpr
import Lean.Elab.PreDefinition.Structural.IndGroupInfo

namespace Lean.Elab.Structural


/--
Information about the argument of interest of a structurally recursive function.

The `Expr`s in this data structure expect the `fixedParams` to be in scope, but not the other
parameters of the function. This ensures that this data structure makes sense in the other functions
of a mutually recursive group.
-/
structure RecArgInfo where
  /-- the name of the recursive function -/
  fnName       : Name
  /-- the fixed prefix of arguments of the function we are trying to justify termination using structural recursion. -/
  numFixed     : Nat
  /-- position (counted including fixed prefix) of the argument we are recursing on -/
  recArgPos    : Nat
  /-- position (counted including fixed prefix) of the indices of the inductive datatype we are recursing on -/
  indicesPos   : Array Nat
  /-- The inductive group (with parameters) of the argument's type -/
  indGroupInst : IndGroupInst
  /--
  index of the inductive datatype of the argument we are recursing on.
  If `< indAll.all`, a normal data type, else an auxiliary data type due to nested recursion
  -/
  indIdx       : Nat
deriving Inhabited, Repr

/--
If `xs` are the parameters of the functions (excluding fixed prefix), partitions them
into indices and major arguments, and other parameters.
-/
def RecArgInfo.pickIndicesMajor (info : RecArgInfo) (xs : Array Expr) : (Array Expr × Array Expr) := Id.run do
  -- First indices and major arg, using the order they appear in `info.indicesPos`
  let mut indexMajorArgs := #[]
  let indexMajorPos := info.indicesPos.push info.recArgPos
  for j in indexMajorPos do
    assert! info.numFixed ≤ j && j - info.numFixed < xs.size
    indexMajorArgs := indexMajorArgs.push xs[j - info.numFixed]!
  -- Then the other arguments, in the order they appear in `xs`
  let mut otherArgs := #[]
  for h : i in [:xs.size] do
    unless indexMajorPos.contains (i + info.numFixed) do
      otherArgs := otherArgs.push xs[i]
  return (indexMajorArgs, otherArgs)

/--
Name of the recursive data type. Assumes that it is not one of the auxiliary ones.
-/
def RecArgInfo.indName! (info : RecArgInfo) : Name :=
  info.indGroupInst.all[info.indIdx]!

end Lean.Elab.Structural
