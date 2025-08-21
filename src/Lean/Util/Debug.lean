/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

prelude
public import Lean.Util.Trace

public section

/-!
# Simple debugging and consistency check framework

During development it is useful to enable expensive consistency checks
and sometimes even tweak behavior to stress test a component.

It is useful to be able to conditionally enable these in a consistent way,
and to leave them in for future use.

Like trace messages, debugging classes can be enabled using
`set_option debug.class.name true`.
This enables code for `debug.class.name` as well as child classes
that are explicitly marked as inherited (see `registerDebugClass`).

This module provides the API to manage debugging classes and enabling debugging code.
The key entry points are:
- ``registerDebugClass `class.name`` registers a debugging class.
- `Lean.isDebuggingEnabledFor` determines whether a debugging class is enabled.
- `debug[class.name] doElem` is a `doElem` for conveniently making use of debugging classes in `do` notation.

Try to follow these guidelines:
1. **No heisenbugs.** Make sure debugging code avoids creating side effects,
   unless the side effects are a documented intent.
2. **Document the purpose.** Each debugging class should come with a description
   that explains what consistency checks or side effects the class enables.
3. **Good defaults.** Enabling a debug class for a module should enable reasonable
   consistency checks, without needing to enable additional options.

-/

namespace Lean

builtin_initialize inheritedDebugOptions : IO.Ref (Std.HashSet Name) ← IO.mkRef ∅

class MonadDebug (m : Type → Type) where
  /--
  Like `MonadTrace`, should return the value of `inheritedDebugOptions.get`,
  which does not change after initialization.
  As `IO.Ref.get` may be too expensive on frequent and multi-threaded access,
  the value may want to be cached, which is done in the stdlib in `CoreM`.
  -/
  getInheritedDebugOptions : m (Std.HashSet Name) := by exact inheritedDebugOptions.get

instance (m n) [MonadLift m n] [MonadDebug m] : MonadDebug n where
  getInheritedDebugOptions := liftM (MonadDebug.getInheritedDebugOptions : m _)

variable {α : Type} {m : Type → Type} [Monad m] [MonadDebug m] [MonadOptions m] [MonadLiftT IO m]

def checkDebugOption (inherited : Std.HashSet Name) (opts : Options) (cls : Name) : Bool :=
  !opts.isEmpty && go (`debug ++ cls)
where
  go (opt : Name) : Bool :=
    if let some enabled := opts.get? opt then
      enabled
    else if let .str parent _ := opt then
      inherited.contains opt && go parent
    else
      false

def isDebuggingEnabledFor (cls : Name) : m Bool := do
  return checkDebugOption (← MonadDebug.getInheritedDebugOptions) (← getOptions) cls

/--
Registers a debug class.
The `descr` option is used to create a `debug` option description of the form "enable/disable debugging option: {descr}".

By default, debug classes are not inherited;
that is, `set_option debug.foo true "descr"` does not imply `set_option debug.foo.bar true`.
Calling ``registerDebugClass `foo.bar "descr" (inherited := true)`` enables this inheritance
on an opt-in basis.
-/
def registerDebugClass (debugClassName : Name) (descr : String) (inherited := false) (defValue := false) (ref : Name := by exact decl_name%) : IO Unit := do
  let optionName := `debug ++ debugClassName
  registerOption optionName {
    declName := ref
    group := "debug"
    defValue
    descr := s!"enable/disable debugging option: {descr}"
  }
  if inherited then
    inheritedDebugOptions.modify (·.insert optionName)

def expandDebugMacro (id : Syntax) (d : TSyntax `doElem) : MacroM (TSyntax `doElem) := do
  `(doElem| do
    let cls := $(quote id.getId.eraseMacroScopes)
    if (← Lean.isDebuggingEnabledFor cls) then
      $d:doElem)

macro "debug[" id:ident "]" d:doElem : doElem => do
  expandDebugMacro id d

end Lean
