import Lean

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Command Lean.PrettyPrinter

syntax (name := roundtrip) "#roundtrip " ident : command

@[commandElab roundtrip] def elabRoundtrip : CommandElab
| `(#roundtrip%$tk $name:ident) => withoutModifyingEnv do
  let [name] ← resolveGlobalConst name | throwError "cannot resolve name"
  let some cInfo ← (← getEnv).find? name | throwError "no such decl: {name}"
  let ns := cInfo.name.getRoot
  let cmdStx  ← liftTermElabM none do
    let typeStx  ← delab ns [] cInfo.type {}
    let valueStx ← delab ns [] cInfo.value! {}
    `(noncomputable def $(mkIdent (ns ++ `foo)):declId : $typeStx:term := $valueStx:term)
  elabCommand cmdStx

| _ => throwUnsupportedSyntax

#roundtrip Nat.add
#roundtrip Std.Range.forIn.loop

def hasMonadInst {α : Type u} {m : Type u → Type v} [Monad m] (x : m α) : m α := x

#roundtrip hasMonadInst

