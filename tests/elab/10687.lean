import Lean

/-! Macros in `mutual` should preserve remaining `mutual` items. -/

open Lean Elab Command Lean.PrettyPrinter

private def trace [Repr α] (name : String) (p : IO α) : IO α := do
  IO.println s!"tracing: {name}"
  p

syntax (name := traced) "#traced " declModifiers "def " ident optDeclSig " := " term : command

@[macro traced] def elabTracedDef : Macro := fun stx => do
  match stx with
  | `(command| #traced $mods:declModifiers def $name:ident $sig:optDeclSig := $body:term) => do
    let nameStr := name.getId.toString
    let name_ := mkIdent (name.getId.appendAfter "_")
    let args := sig.raw[0].getArgs
    let mut argNames := #[]
    for arg in args do
      argNames := argNames.push (mkIdent (arg[1][0].getId))
    -- Generate the first definition: def foo_ : Type := body
    let def1 := ← `(command| $mods:declModifiers def $name_ $sig:optDeclSig := $body)
    -- Generate the second definition: def foo : Type := trace "foo" foo_
    let traceCall := ← `(trace $(quote nameStr) ($name_ $[ $argNames:ident ]*))
    let def2 := ← `(command| $mods:declModifiers def $name $sig:optDeclSig := $traceCall)
    let res <- `($def1:command
                 $def2:command)
    dbg_trace "{res.raw.prettyPrint}"
    return res
  | _ => Macro.throwUnsupported

#traced
def foo (x : IO Nat) : IO Nat := x

#eval foo (pure 5)

mutual

--#traced
private partial def baz (x : IO Nat) : IO Nat :=
  bar (pure 7)

#traced  -- this previously discarded `baz`
private partial def bar (x : IO Nat) : IO Nat :=
  baz (pure 5)

end -- mutual
