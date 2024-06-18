prelude
import Lean.Elab.Command
import Lean.Parser.Tactic.Doc

namespace Lean.Elab.Tactic.Doc
open Lean.Parser.Tactic.Doc

open Lean Elab Command in
elab_rules : command
  | `(tactic_extension $_) => throwError "Missing documentation comment"
  | `($doc:docComment tactic_extension $tac) => do
    let tacName ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo tac
    if let some tgt' ← aliasOfTactic tacName then
        throwError "'{tacName}' is an alias of '{tgt'}'"
    modifyEnv (tacticDocExtExt.addEntry · (tacName, doc.getDocString))

elab_rules : command
  | `($[$doc:docComment]? register_tactic_tag $tag $user) => do
    let docstring ← doc.mapM getDocStringText
    modifyEnv (knownTacticTagExt.addEntry · (tag.getId, user.getString, docstring))
