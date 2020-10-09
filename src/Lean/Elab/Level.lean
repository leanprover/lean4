/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.LevelDefEq
import Lean.Elab.Exception
import Lean.Elab.Log
new_frontend

namespace Lean.Elab.Level

structure Context :=
(ref        : Syntax)
(levelNames : List Name)

structure State :=
(ngen : NameGenerator)
(mctx : MetavarContext)

abbrev LevelElabM := ReaderT Context (EStateM Exception State)

instance : Ref LevelElabM :=
{ getRef      := do return (← read).ref,
  withRef     := fun ref x => adaptReader (fun ctx => { ctx with ref := ref }) x }

instance : AddMessageContext LevelElabM :=
{ addMessageContext := fun msg => pure msg }

instance : MonadNameGenerator LevelElabM :=
{ getNGen := do return (← get).ngen,
  setNGen := fun ngen => modify fun s => { s with ngen := ngen } }

def mkFreshLevelMVar : LevelElabM Level := do
let mvarId ← mkFreshId
modify fun s => { s with mctx := s.mctx.addLevelMVarDecl mvarId }
return mkLevelMVar mvarId

partial def elabLevel : Syntax → LevelElabM Level
| stx => withRef stx do
  let kind := stx.getKind
  if kind == `Lean.Parser.Level.paren then
    elabLevel (stx.getArg 1)
  else if kind == `Lean.Parser.Level.max then
    let args := (stx.getArg 1).getArgs
    let lvl ← elabLevel args.back
    args.foldrRangeM 0 (args.size - 1)
      (fun stx lvl => do
        let arg ← elabLevel stx
        pure (mkLevelMax lvl arg))
      lvl
  else if kind == `Lean.Parser.Level.imax then
    let args := (stx.getArg 1).getArgs
    let lvl ← elabLevel args.back
    args.foldrRangeM 0 (args.size - 1)
      (fun stx lvl => do
        let arg ← elabLevel stx
        pure (mkLevelIMax lvl arg))
      lvl
  else if kind == `Lean.Parser.Level.hole then
    mkFreshLevelMVar
  else if kind == numLitKind then
    match stx.isNatLit? with
    | some val => pure (Level.ofNat val)
    | none     => throwIllFormedSyntax
  else if kind == identKind then
    let paramName := stx.getId
    unless ((← read).levelNames.contains paramName) do
      throwError ("unknown universe level " ++ paramName)
    return mkLevelParam paramName
  else if kind == `Lean.Parser.Level.addLit then
    let lvl ← elabLevel (stx.getArg 0)
    match (stx.getArg 2).isNatLit? with
    | some val => pure (lvl.addOffset val)
    | none     => throwIllFormedSyntax
  else
    throwError "unexpected universe level syntax kind"

end Lean.Elab.Level
