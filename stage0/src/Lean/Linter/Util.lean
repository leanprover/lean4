import Lean.Data.Options
import Lean.Elab.Command
import Lean.Server.InfoUtils

namespace Lean.Linter

register_builtin_option linter.all : Bool := {
  defValue := false
  descr := "enable all linters"
}

def getLinterAll (o : Options) (defValue := linter.all.defValue) : Bool := o.get linter.all.name defValue

def getLinterValue (opt : Lean.Option Bool) (o : Options) : Bool := o.get opt.name (getLinterAll o opt.defValue)

open Lean.Elab Lean.Elab.Command

def logLint (linterOption : Lean.Option Bool) (stx : Syntax) (msg : MessageData) : CommandElabM Unit :=
  logWarningAt stx (.tagged linterOption.name m!"{msg} [{linterOption.name}]")

/-- Go upwards through the given `tree` starting from the smallest node that
contains the given `range` and collect all `MacroExpansionInfo`s on the way up.
The result is `some []` if no `MacroExpansionInfo` was found on the way and
`none` if no `InfoTree` node was found that covers the given `range`.

Return the result reversed, s.t. the macro expansion that would be applied to
the original syntax first is the first element of the returned list. -/
def collectMacroExpansions? {m} [Monad m] (range : String.Range) (tree : Elab.InfoTree) : m <| Option <| List Elab.MacroExpansionInfo := do
    if let .some <| .some result ← go then
      return some result.reverse
    else
      return none
where
  go : m <| Option <| Option <| List Elab.MacroExpansionInfo := tree.visitM (postNode := fun _ i _ results => do
    let results := results |>.filterMap id |>.filterMap id

    -- we expect that at most one InfoTree child returns a result
    if let results :: _ := results then
      if let .ofMacroExpansionInfo i := i then
        return some <| i :: results
      else
        return some results
    else if i.contains range.start && i.contains (includeStop := true) range.stop then
      if let .ofMacroExpansionInfo i := i then
        return some [i]
      else
        return some []
    else
      return none)

/-- List of `Syntax` nodes in which each succeeding element is the parent of
the current. The associated index is the index of the preceding element in the
list of children of the current element. -/
abbrev SyntaxStack := List (Syntax × Nat)

/-- Go upwards through the given `root` syntax starting from `child` and
collect all `Syntax` nodes on the way up.

Return `none` if the `child` is not found in `root`. -/
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

/-- Compare the `SyntaxNodeKind`s in `pattern` to those of the `Syntax`
elements in `stack`. Return `false` if `stack` is shorter than `pattern`. -/
def stackMatches (stack : SyntaxStack) (pattern : List $ Option SyntaxNodeKind) : Bool :=
  stack.length >= pattern.length &&
  (stack
    |>.zipWith (fun (s, _) p => p |>.map (s.isOfKind ·) |>.getD true) pattern
    |>.all id)

abbrev IgnoreFunction := Syntax → SyntaxStack → Options → Bool

end Lean.Linter
