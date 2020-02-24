/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.LevelDefEq
import Init.Lean.Elab.Exception
import Init.Lean.Elab.Log

namespace Lean
namespace Elab
namespace Level

structure Context :=
(fileName   : String)
(fileMap    : FileMap)
(cmdPos     : String.Pos)
(levelNames : List Name)

structure State :=
(ngen : NameGenerator)
(mctx : MetavarContext)

abbrev LevelElabM := ReaderT Context (EStateM Exception State)

instance LevelElabM.MonadLog : MonadPosInfo LevelElabM :=
{ getCmdPos   := do ctx ← read; pure ctx.cmdPos,
  getFileMap  := do ctx ← read; pure ctx.fileMap,
  getFileName := do ctx ← read; pure ctx.fileName,
  addContext  := fun msg => pure msg }

def mkFreshId : LevelElabM Name := do
s ← get;
let id := s.ngen.curr;
modify $ fun s => { ngen := s.ngen.next, .. s };
pure id

def mkFreshLevelMVar : LevelElabM Level := do
mvarId ← mkFreshId;
modify $ fun s => { mctx := s.mctx.addLevelMVarDecl mvarId, .. s};
pure $ mkLevelMVar mvarId

partial def elabLevel : Syntax → LevelElabM Level
| stx => do
  let kind := stx.getKind;
  if kind == `Lean.Parser.Level.paren then
    elabLevel (stx.getArg 1)
  else if kind == `Lean.Parser.Level.max then do
    let args := (stx.getArg 1).getArgs;
    lvl ← elabLevel args.back;
    args.foldrRangeM 0 (args.size - 1)
      (fun stx lvl => do
        arg ← elabLevel stx;
        pure (mkLevelMax lvl arg))
      lvl
  else if kind == `Lean.Parser.Level.imax then do
    let args := (stx.getArg 1).getArgs;
    lvl ← elabLevel args.back;
    args.foldrRangeM 0 (args.size - 1)
      (fun stx lvl => do
        arg ← elabLevel stx;
        pure (mkLevelIMax lvl arg))
      lvl
  else if kind == `Lean.Parser.Level.hole then do
    mkFreshLevelMVar
  else if kind == `Lean.Parser.Level.num then do
    match (stx.getArg 0).isNatLit? with
    | some val => pure (Level.ofNat val)
    | none     => throwError stx "ill-formed universe level syntax"
  else if kind == `Lean.Parser.Level.ident then do
    let paramName := stx.getIdAt 0;
    ctx ← read;
    unless (ctx.levelNames.contains paramName) $ throwError stx ("unknown universe level " ++ paramName);
    pure $ mkLevelParam paramName
  else if kind == `Lean.Parser.Level.addLit then do
    lvl ← elabLevel (stx.getArg 0);
    match (stx.getArg 2).isNatLit? with
    | some val => pure (lvl.addOffset val)
    | none     => throwError stx "ill-formed universe level syntax"
  else
    throwError stx "unexpected universe level syntax kind"

end Level

export Level (LevelElabM)

end Elab
end Lean
