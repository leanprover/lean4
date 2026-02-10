/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Basic
import Init.Omega

public section

namespace Lean.Compiler

inductive SpecializeAttributeKind where
  | specialize | nospecialize
  deriving Inhabited, BEq

/--
Marks a definition to never be specialized during code generation.
-/
@[builtin_doc]
builtin_initialize nospecializeAttr : TagAttribute ←
  registerTagAttribute `nospecialize "mark definition to never be specialized"

private def elabSpecArgs (declName : Name) (args : Array Syntax) : MetaM (Array Nat) := do
  if args.isEmpty then return #[]
  let info ← getConstInfo declName
  Meta.forallTelescopeReducing info.type fun xs _ => do
    let argNames ← xs.mapM fun x => x.fvarId!.getUserName
    let mut result := #[]
    for arg in args do
      if let some idx := arg.isNatLit? then
        if idx == 0 then throwErrorAt arg "Invalid specialization argument index `0`: Index must be greater than 0"
        let idx := idx - 1
        if h : idx >= argNames.size then
          throwErrorAt arg "Invalid argument index `{idx}`: `{.ofConstName declName}` has only {argNames.size} arguments"
        else
          if result.contains idx then throwErrorAt arg "Invalid specialization argument index `{idx + 1}`: \
            The argument at this index (`{argNames[idx]}`) has already been specified as a specialization candidate"
          result := result.push idx
      else
        let argName := arg.getId
        if let some idx := argNames.idxOf? argName then
          if result.contains idx then throwErrorAt arg "Invalid specialization argument name `{argName}`: \
            It has already been specified as a specialization candidate"
          result := result.push idx
        else
          throwErrorAt arg "Invalid specialization argument name `{argName}`: `{.ofConstName declName}` does not have an argument with this name"
    return result.qsort (·<·)

/--
Marks a definition to always be specialized during code generation.

Specialization is an optimization in the code generator for generating variants of a function that
are specialized to specific parameter values. This is in particular useful for functions that take
other functions as parameters: Usually when passing functions as parameters, a closure needs to be
allocated that will then be called. Using `@[specialize]` prevents both of these operations by
using the provided function directly in the specialization of the inner function.

`@[specialize]` can take additional arguments for the parameter names or indices (starting at 1) of
the parameters that should be specialized. By default, instance and function parameters are
specialized.
-/
@[builtin_doc]
builtin_initialize specializeAttr : ParametricAttribute (Array Nat) ←
  registerParametricAttribute {
    name := `specialize
    descr := "mark definition to always be specialized"
    getParam := fun declName stx => do
      let args := stx[1].getArgs
      elabSpecArgs declName args |>.run'
  }

def getSpecializationArgs? (env : Environment) (declName : Name) : Option (Array Nat) :=
  specializeAttr.getParam? env declName

def hasSpecializeAttribute (env : Environment) (declName : Name) : Bool :=
  getSpecializationArgs? env declName |>.isSome

def hasNospecializeAttribute (env : Environment) (declName : Name) : Bool :=
  nospecializeAttr.hasTag env declName

end Lean.Compiler
