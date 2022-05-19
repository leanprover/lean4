import Lean.Data.Options
import Lean.Elab.Command
import Lean.Server.InfoUtils

namespace Lean.Linter

register_builtin_option linter.nolint : Bool := {
  defValue := false,
  descr := "disable all linters"
}

open Lean.Elab Lean.Elab.Command

def publishMessage
  (content : String) (range : String.Range) (severity : MessageSeverity := .information) : CommandElabM Unit :=
do
  let ctx := (← read)
  let messages := (← get).messages |>.add (mkMessageCore ctx.fileName ctx.fileMap content severity range.start range.stop)
  modify ({ · with messages := messages })

abbrev SyntaxStack := List (Syntax × Nat)

partial def anyWithStack (pred : Syntax → SyntaxStack → Bool) (stx : Syntax) : Bool :=
  let rec go (stack : SyntaxStack) (stx : Syntax) : Bool := Id.run <| do
    if pred stx stack then
      return true
    for i in List.range stx.getNumArgs do
      if go ((stx, i) :: stack) stx[i] then
        return true
    return false
  go [] stx

def stackMatches (stack : SyntaxStack) (pattern : List $ Option SyntaxNodeKind) : Bool :=
  stack.length >= pattern.length &&
  (stack
    |>.zipWith (fun (s, _) p => p |>.map (s.isOfKind ·) |>.getD true) pattern
    |>.all id)

end Lean.Linter
