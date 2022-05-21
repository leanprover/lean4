import Lean.Data.Options
import Lean.Elab.Command
import Lean.Server.InfoUtils

namespace Lean.Linter

register_builtin_option linter.all : Bool := {
  defValue := true,
  descr := "enable all linters"
}

def getLinterAll (o : Options) : Bool := o.get linter.all.name linter.all.defValue

open Lean.Elab Lean.Elab.Command

def publishMessage
  (content : String) (range : String.Range) (severity : MessageSeverity := .warning) : CommandElabM Unit :=
do
  let ctx := (← read)
  let messages := (← get).messages |>.add (mkMessageCore ctx.fileName ctx.fileMap content severity range.start range.stop)
  modify ({ · with messages := messages })

abbrev SyntaxStack := List (Syntax × Nat)

partial def findSyntaxStack? (root child : Syntax) : Option SyntaxStack := Id.run <| do
  let some childRange := child.getRange?
    | none
  let rec go (stack : SyntaxStack) (stx : Syntax) : Option SyntaxStack := Id.run <| do
    let some range := stx.getRange?
      | none
    if !range.contains childRange.start then
      return none

    if range == childRange && stx.getKind == child.getKind then
      return stack

    for i in List.range stx.getNumArgs do
      if let some resultStack := go ((stx, i) :: stack) stx[i] then
        return resultStack
    return none
  go [] root

def stackMatches (stack : SyntaxStack) (pattern : List $ Option SyntaxNodeKind) : Bool :=
  stack.length >= pattern.length &&
  (stack
    |>.zipWith (fun (s, _) p => p |>.map (s.isOfKind ·) |>.getD true) pattern
    |>.all id)

end Lean.Linter
