/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Lean.Elab.Command
public import Lean.Linter.Basic


namespace Lean.Linter
open Elab.Command

private structure TopDownSkipQuot where
  stx : Syntax

def topDownSkipQuot (stx : Syntax) : TopDownSkipQuot := ⟨stx⟩

partial instance [Monad m] : ForIn m TopDownSkipQuot Syntax where
  forIn := fun ⟨stx⟩ init f => do
    let rec @[specialize] loop stx b [Inhabited (type_of% b)] := do
      if stx.isQuot then return ForInStep.yield b
      match (← f stx b) with
      | ForInStep.yield b' =>
        let mut b := b'
        if let Syntax.node _ _ args := stx then
          for arg in args do
            match (← loop arg b) with
            | ForInStep.yield b' => b := b'
            | ForInStep.done b'  => return ForInStep.done b'
        return ForInStep.yield b
      | ForInStep.done b => return ForInStep.done b
    match (← @loop stx init ⟨init⟩) with
    | ForInStep.yield b => return b
    | ForInStep.done b  => return b

def getGlobalAttributesIn? : Syntax → Option (Ident × Array (TSyntax `attr))
  | `(attribute [$x,*] $id in $_) =>
    let xs := x.getElems.filterMap fun a => match a.raw with
      | `(Parser.Command.eraseAttr| -$_) => none
      | `(Parser.Term.attrInstance| local $_attr:attr) => none
      | `(Parser.Term.attrInstance| scoped $_attr:attr) => none
      | `(attr| $a) => some a
    (id, xs)
  | _ => default

def globalAttributeIn : Linter where run := withSetOptionIn fun stx => do
  for s in topDownSkipQuot stx do
    if let some (id, nonScopedNorLocal) := getGlobalAttributesIn? s then
      for attr in nonScopedNorLocal do
        logErrorAt attr
          m!"Despite the `in`, the attribute {attr} is added globally to {id}\n\
          please remove the `in` or make this a `local {attr}`"

builtin_initialize addLinter globalAttributeIn

end Lean.Linter
