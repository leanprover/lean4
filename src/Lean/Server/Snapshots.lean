import Init.System.IO

import Lean.Elab.Import
import Lean.Elab.Command

/-! One can think of this module as being a partial reimplementation
of Lean.Elab.Frontend which also stores a snapshot of the world after
each command. Importantly, we allow starting compilation from any
snapshot/position in the file for interactive editing purposes. -/

namespace Lean
namespace Elab
namespace Snapshots

/-- What Lean knows about the world after each command. -/
structure Snapshot :=
/- The (ln,col) after the command. *Not* the
same as mpState.pos as that's a linear Nat. -/
--(pos : Position)
(env : Environment)
(mpState : Parser.ModuleParserState)
--(opts : Options) TODO these are set_option options right? might need to store them

def Snapshot.pos (s : Snapshot) : String.Pos := s.mpState.pos

/-- Compiles the next command occuring after the given snapshot.
If there is no next command, returns `none`. -/
-- NOTE(WN): this code is really very similar to Elab.Frontend.
-- Is there a point in generalizing it over "store snapshots"/"don't store snapshots" via
-- changing the FrontendM monad? I say no because it would likely result in
-- confusing isServer? conditionals.
-- TODO(WN): should probably take inputCtx and live in some SnapshotsM := ReaderT Context (EIO Empty)
def compileNextCmd (contents : String) (msgLog : MessageLog) (snap : Snapshot)
  : IO (Option (MessageLog × Snapshot)) := do
let inputCtx := Parser.mkInputContext contents "<input>";
let (cmdStx, cmdParserState, msgLog) :=
  Parser.parseCommand snap.env inputCtx snap.mpState msgLog;
e ← IO.stderr;
e.putStrLn $ "Cmd @ " ++ toString snap.pos ++ " = " ++ (toString $ cmdStx.formatStx none true);
if Parser.isEOI cmdStx || Parser.isExitCommand cmdStx then
  pure none
else do
  cmdStateRef ← IO.mkRef $ Elab.Command.mkState snap.env msgLog { : Options };
  let cmdCtx : Elab.Command.Context :=
    { cmdPos := snap.pos
    , stateRef := cmdStateRef
    , fileName := inputCtx.fileName
    , fileMap := inputCtx.fileMap };
  EIO.adaptExcept
    (fun e => unreachable!) -- TODO(WN): ignoring exceptions ok here?
    (Elab.Command.withLogging
      (Elab.Command.elabCommand cmdStx)
      cmdCtx);
  postCmdState ← cmdStateRef.get;
  let postCmdSnap : Snapshot := ⟨postCmdState.env, cmdParserState⟩;
  pure $ some (postCmdState.messages, postCmdSnap)

partial def compileCmdsAfter (contents : String) : MessageLog → Snapshot
  → IO (MessageLog × List Snapshot)
| msgLog, snap => do
  cmdOut ← compileNextCmd contents msgLog snap;
  match cmdOut with
  | some (msgLog, snap) => do
    (msgLog, snaps) ← compileCmdsAfter msgLog snap;
    pure (msgLog, snap :: snaps)
  | none => pure (msgLog, [])

end Snapshots
end Elab
end Lean
