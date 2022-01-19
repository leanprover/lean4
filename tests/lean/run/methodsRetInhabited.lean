open Lean

def exec (x : MacroM α) : Option α :=
  match x {
      mainModule := `Expander
      currMacroScope := 0
      ref := default
      methods := default } { macroScope := 0 } with
    | EStateM.Result.ok a s => a
    | _ => none

def tst : MacroM String := do
  let n ← Macro.getCurrNamespace
  return toString n

#eval exec tst
