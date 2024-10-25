/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Elab.Term

namespace Lean.Elab.Term

/--
Auxiliary inductive datatype for combining unelaborated syntax
and already elaborated expressions. It is used to elaborate applications.
-/
inductive Arg where
  | stx  (val : Syntax)
  | expr (val : Expr)
  deriving Inhabited

/-- Named arguments created using the notation `(x := val)`. -/
structure NamedArg where
  ref  : Syntax := Syntax.missing
  name : Name
  val  : Arg
  /-- If `true`, then make all parameters that depend on this one become implicit.
  This is used for projection notation, since structure parameters might be explicit for classes. -/
  suppressDeps : Bool := false
  deriving Inhabited

/--
  Add a new named argument to `namedArgs`, and throw an error if it already contains a named argument
  with the same name. -/
def addNamedArg (namedArgs : Array NamedArg) (namedArg : NamedArg) : MetaM (Array NamedArg) := do
  if namedArgs.any (namedArg.name == ·.name) then
    throwError "argument '{namedArg.name}' was already set"
  return namedArgs.push namedArg

partial def expandArgs (args : Array Syntax) : MetaM (Array NamedArg × Array Arg × Bool) := do
  let (args, ellipsis) :=
    if args.isEmpty then
      (args, false)
    else if args.back.isOfKind ``Lean.Parser.Term.ellipsis then
      (args.pop, true)
    else
      (args, false)
  let (namedArgs, args) ← args.foldlM (init := (#[], #[])) fun (namedArgs, args) stx => do
    if stx.getKind == ``Lean.Parser.Term.namedArgument then
      -- trailing_tparser try ("(" >> ident >> " := ") >> termParser >> ")"
      let name := stx[1].getId.eraseMacroScopes
      let val  := stx[3]
      let namedArgs ← addNamedArg namedArgs { ref := stx, name := name, val := Arg.stx val }
      return (namedArgs, args)
    else if stx.getKind == ``Lean.Parser.Term.ellipsis then
      throwErrorAt stx "unexpected '..'"
    else
      return (namedArgs, args.push $ Arg.stx stx)
  return (namedArgs, args, ellipsis)

def expandApp (stx : Syntax) : MetaM (Syntax × Array NamedArg × Array Arg × Bool) := do
  let (namedArgs, args, ellipsis) ← expandArgs stx[1].getArgs
  return (stx[0], namedArgs, args, ellipsis)

end Lean.Elab.Term
