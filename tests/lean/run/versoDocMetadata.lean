import Lean.Elab.Command
import Lean.Elab.DocString.Builtin

set_option doc.verso true

/-!
# Tests for Verso Docstring Metadata

These tests ensure that the right information is being saved for Verso docstrings by the builtin
elaborators.
-/

/-!
## Infrastructure

First, some test infrastructure for checking docstring contents.
-/

section
open Lean Elab Command Term

partial def containsMetadataMatchingInline [Monad m] (inline : Doc.Inline ElabInline) (p : Dynamic → m Bool) : m Bool :=
  match inline with
  | .text .. | .image .. | .linebreak .. | .math .. | .code .. => pure false
  | .concat xs | .bold xs | .emph xs | .link xs _ | .footnote _ xs => xs.anyM (containsMetadataMatchingInline · p)
  | .other container content =>
    p container.val <||> content.anyM (containsMetadataMatchingInline · p)


partial def containsMetadataMatchingBlock [Monad m] (block : Doc.Block ElabInline ElabBlock) (p : Dynamic → m Bool) : m Bool :=
  match block with
  | .code .. => pure false
  | .concat xs | .blockquote xs => xs.anyM (containsMetadataMatchingBlock · p)
  | .ol _ items | .ul items =>
    items.anyM fun ⟨bs⟩ => bs.anyM (containsMetadataMatchingBlock · p)
  | .dl items =>
    items.anyM fun ⟨dt, dd⟩ =>
      dt.anyM (containsMetadataMatchingInline · p) <||> dd.anyM (containsMetadataMatchingBlock · p)
  | .para xs => xs.anyM (containsMetadataMatchingInline · p)
  | .other container content =>
      p container.val <||> content.anyM (containsMetadataMatchingBlock · p)

partial def containsMetadataMatchingPart [Monad m] (part : Doc.Part ElabInline ElabBlock Empty) (p : Dynamic → m Bool) : m Bool :=
  part.title.anyM (containsMetadataMatchingInline · p) <||>
  part.content.anyM (containsMetadataMatchingBlock · p) <||>
  part.subParts.anyM (containsMetadataMatchingPart · p)

def containsMetadataMatching [Monad m] (docs : VersoDocString) (p : Dynamic → m Bool) : m Bool :=
  docs.text.anyM (containsMetadataMatchingBlock · p) <||>
  docs.subsections.anyM (containsMetadataMatchingPart · p)

syntax (name := check) "#verso_docs_contain " ident " where " term : command

@[command_elab check]
unsafe def elabChecker : CommandElab := fun
  | `(command|#verso_docs_contain $name:ident where $predicate:term) => withoutModifyingEnv do
    let env ← getEnv
    let n ← runTermElabM fun _ => mkFreshUserName `pred
    elabCommand <| ← `(def $(mkIdent n) : Dynamic → TermElabM Bool := $predicate)
    let pred ← evalConst (Dynamic → TermElabM Bool) n
    let declName ← runTermElabM fun _ => do realizeGlobalConstNoOverloadWithInfo name
    let verso ←
      match (← findInternalDocString? env declName (includeBuiltin := true)) with
      | some (.inl ..) => throwError m!"`{.ofConstName declName}` has a Markdown docstring"
      | some (.inr verso) => pure verso
      | none => throwError m!"`{.ofConstName declName}` has no docstring"
    if ← runTermElabM fun _ => containsMetadataMatching verso pred then
      pure ()
    else
      throwError "No metadata satisfied the predicate"
  | _ => throwUnsupportedSyntax

/-!
## Tests

Here, we test the expected metadata for code blocks and inline elements.
-/

/--
```lean
def y := x
```
-/
def x := ()

#verso_docs_contain x where fun y => do
  if let some v := y.get? Doc.Data.LeanBlock then
    let hasDef := v.commands.code.any fun x =>
      x.1 == "def" && x.2 matches some .keyword
    let hasY := v.commands.code.any fun x =>
      x.1 == "y" && x.2 matches some (.const ..)
    let hasX := v.commands.code.any fun x =>
      x.1 == "x" && x.2 matches some (.const ``x ..)
    pure <| hasDef && hasY && hasX
  else
    pure false

/--
{lean}`foo x`
-/
def foo (x : Nat) := Nat.succ x

#verso_docs_contain foo where fun y => do
  if let some v := y.get? Doc.Data.LeanTerm then
    let hasFoo := v.term.code.any fun x =>
      x.1 == "foo" && x.2 matches some (.const ``foo ..)
    let hasX := v.term.code.any fun x =>
      x.1 == "x" && x.2 matches some (.var `x ..)
    pure <| hasFoo && hasX
  else
    pure false
