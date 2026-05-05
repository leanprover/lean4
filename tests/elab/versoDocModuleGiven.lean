/-
Tests that `{given}` in Verso module docs does not leak metavariables or
typeclass constraints into subsequent declarations, and that unsolved
metavariables in `{given}` types are reported as errors.
-/
import Lean

set_option doc.verso true
set_option doc.verso.module true
-- Universe metavariable indices are fed by a global counter and can shift if
-- anything upstream changes; suppress them so `#guard_msgs` stays stable.
set_option pp.mvars.levels false

open Lean Doc Elab Term

/-!
# Helpers

This section contains helpers used in the tests in this file.
-/

-- Helpers to inspect elaborated doc content
private def showDocHl (code : Array (String × Option DocHighlight)) : Std.Format :=
  .group (behavior := .fill) <| code.foldl (init := .nil) fun
    | soFar, (str, none) => soFar.append str
    | soFar, (str, some hl) => soFar ++ .line ++ (entaggen hl str)
where
  entaggen hl str := (opener hl : Format) ++ str ++ closer hl
  opener
    | .const x sig => s!"<const name=\"{x}\" sig=\"{sig}\">"
    | .var x _fv ty => s!"<var name=\"{x}\" type=\"{ty}\">"
    | .field x sig => s!"<field name=\"{x}\" sig=\"{sig}\">"
    | .option x d => s!"<option name=\"{x}\" decl=\"{d}\">"
    | .keyword => "<kw>"
    | .literal k (some ty) => s!"<lit kind=\"{k}\" type=\"{ty}\">"
    | .literal k none => s!"<lit kind=\"{k}\" type=none>"
  closer
    | .const .. => "</const>"
    | .var .. => "</var>"
    | .field .. => "</field>"
    | .option .. => "</option>"
    | .keyword => "</kw>"
    | .literal .. => "</lit>"

private def docCodeStr (dc : DocCode) : String :=
  showDocHl dc.code |>.pretty (width := 70)

/--
Finds the highlighted code segments in an inline element.
-/
private partial def findInInline (name : Name) : Inline ElabInline → Array DocCode
  | .other container _ =>
    if container.name == name then
      if let some (lt : Data.LeanTerm) := container.val.get? Data.LeanTerm then
        #[lt.term]
      else #[]
    else #[]
  | .emph xs | .bold xs | .concat xs | .link xs _ | .footnote _ xs =>
    xs.flatMap (findInInline name)
  | .text .. | .code .. | .math .. | .linebreak .. | .image .. => #[]

/--
Finds the highlighted code segments in a block element.
-/
private partial def findInBlock (name : Name) : Block ElabInline ElabBlock → Array DocCode
  | .other container _ =>
    if container.name == name then
      if let some (lb : Data.LeanBlock) := container.val.get? Data.LeanBlock then
        #[lb.commands]
      else if let some (lt : Data.LeanTerm) := container.val.get? Data.LeanTerm then
        #[lt.term]
      else #[]
    else #[]
  | .para inlines => inlines.flatMap (findInInline name)
  | .concat blocks | .blockquote blocks => blocks.flatMap (findInBlock name)
  | .dl items => items.flatMap fun ⟨x, y⟩ => x.flatMap (findInInline name) ++ y.flatMap (findInBlock name)
  | .ol _ xs | .ul xs => xs.flatMap fun ⟨x⟩ => x.flatMap (findInBlock name)
  | .code .. => #[]

/-! # Tests -/

section ExplicitlyTypedGiven

/-!
Test that {name}`given` produces correct highlights.
-/

-- No error:
#guard_msgs in
/-!
Given {given}`α : Type` and {given}`x : α, y : α` with {givenInstance}`Add α`,
we have {lean}`x + y : α`.
-/

-- Check that the explicitly-typed case produces proper highlights.
#eval show TermElabM Unit from do
  let env ← getEnv
  let docs := getMainVersoModuleDocs env
  let s := docs.snippets.get! 0
  for lt in s.text.flatMap (findInBlock ``Data.LeanTerm) do
    let str := docCodeStr lt
    if str.contains "?" then
      throwError "BUG: metavariable in explicitly-typed given highlight: {str}"
end ExplicitlyTypedGiven

section UnsolvedMetaError
/-!
A {lit}`{given}` with no explicit type that is never constrained should be an error.
-/

/--
error: unresolved metavariable in `given` (type of variable `k`):
  ?m.2
-/
#guard_msgs in
/-!
Given {given}`k`, we consider {lean}`k`.
-/

/-!
A {lit}`{given}` with no explicit type that is only partially constrained should also be an error.
-/

/--
error: don't know how to synthesize implicit argument `α`
  @List.length ?m.6 xs
context:
xs : List ?m.6
⊢ Type _
---
error: unresolved metavariable in `given` (type of variable `xs`):
  List ?m.6
-/
#guard_msgs in
/-!
Given {given}`xs`, we can check the length {lean}`List.length xs`
-/

/-!
Occurrences of a defined name in its own docstring are not automatically instantiated with the
implicit arguments, so this is also an error.
-/
/--
error: don't know how to synthesize implicit argument `α`
  @doubleList ?m.13 xs
context:
α : Type u_1
xs✝ : List α
xs : List ?m.13
⊢ Type _
---
error: unresolved metavariable in `given` (type of variable `xs`):
  List ?m.13
-/
#guard_msgs in
/--
Given {given}`xs`, we can double elements with {lean}`doubleList xs`
-/
def doubleList (xs : List α) : List α := xs.flatMap fun x => [x, x]

/-!
A {lit}`{given}` whose type contains a {lit}`_` placeholder that is never constrained should
report the unresolved type once at the role syntax, plus the standard placeholder diagnostic at
the underscore.
-/

/--
error: unresolved metavariable in `given` (type of variable `xs`):
  List ?m.1
---
error: don't know how to synthesize placeholder for argument `α`
context:
⊢ Type _
-/
#guard_msgs in
/-!
Given {given}`xs : List _`, we have {lean}`xs`.
-/

/-!
A partial type with multiple unresolved holes should still produce a single doc-context error,
plus one standard placeholder error per hole.
-/

/--
error: unresolved metavariable in `given` (type of variable `xs`):
  ?m.1 ⊕ ?m.2
---
error: don't know how to synthesize placeholder for argument `β`
context:
⊢ Type _
---
error: don't know how to synthesize placeholder for argument `α`
context:
⊢ Type _
-/
#guard_msgs in
/-!
Given {given}`xs : Sum _ _`, we have {lean}`xs`.
-/

/-!
A {lit}`{given}` whose value contains an unresolved hole should produce a single doc-context error
naming the variable, plus the standard placeholder/implicit-arg errors for each hole in the value.
-/

/--
error: unresolved metavariable in `given` (value of variable `k`):
  List.length ?m.2
---
error: don't know how to synthesize implicit argument `α`
  @List.length ?m.1 ?m.2
context:
⊢ Type _
---
error: don't know how to synthesize placeholder
context:
⊢ List ?m.1
-/
#guard_msgs in
/-!
Given {given}`k := List.length _ : Nat`, we have {lean}`k`.
-/

end UnsolvedMetaError

section UnconstrainedInstance

-- A givenInstance whose type contains an unresolved hole. One doc-context error points at the
-- role syntax; the standard placeholder error points at the underscore. Neither is attached to
-- the surrounding declaration or a subsequent lean snippet.

/--
error: unresolved metavariable in `givenInstance` (instance type):
  Add ?m.1
---
error: don't know how to synthesize placeholder for argument `α`
context:
⊢ Type _
-/
#guard_msgs in
/-!
Adding {givenInstance}`Add _`, we mention {lean}`Nat.zero`.
-/

-- The fvar instance `Add ?m` is universally applicable to any `Add τ` goal
-- by unifying `?m := τ`, but synth can't commit to assigning an external
-- metavariable, so it gets stuck rather than failing. Default instances
-- don't fire on stuck searches, and the placeholder error is suppressed since
-- `?m` is no longer pending. This matches general Lean TC behavior; recorded
-- here so a future change is noticed.
/--
error: typeclass instance problem is stuck, it is often due to metavariables
  HAdd Nat Nat ?m.10
-/
#guard_msgs in
/-!
Adding {givenInstance}`Add _`, we compute {lean}`(0 : Nat) + 0`.
-/

end UnconstrainedInstance

section InferredTypeResolved
/-!
A {lit}`{given}` with no explicit type that IS constrained by a later {lit}`{lean}` should be fine.
-/

/-!
Given {given}`k`, we have {lean}`k + (1 : Nat)`.
-/
end InferredTypeResolved

section TypeclassConstraintLeak
/-!
Given {given}`β` and {given}`a : β, b : β`, with {givenInstance}`Add β`,
we can form {lean}`a + b`.
-/

-- If typeclass constraints from the preceding moduledoc leak, this theorem could acquire an
-- unwanted `Add` constraint or fail to elaborate. The theorem should have exactly the signature we
-- write, nothing extra.
theorem noExtraConstraints (n m : Nat) : n + m = m + n := Nat.add_comm n m

open Lean in
#eval show TermElabM Unit from do
  let env ← getEnv
  let ci := env.constants.find? ``noExtraConstraints |>.get!
  -- The type should be `∀ (n m : Nat), n + m = m + n` with no metavariables
  if ci.type.hasMVar then
    throwError "BUG: metavariable leaked into theorem type: {ci.type}"
  -- Check that the type doesn't mention `Add` (no extra typeclass constraint)
  let typeStr := toString (← Lean.Meta.MetaM.run' (Lean.PrettyPrinter.ppExpr ci.type))
  if typeStr.contains "Add" then
    throwError "BUG: unwanted `Add` constraint leaked into theorem: {typeStr}"
end TypeclassConstraintLeak

section VariableInteraction
-- Test interaction between section variables and moduledoc {given}
variable (γ : Type) [Add γ]

-- Succeeds because it refers to the section variables:
#guard_msgs in
/-!
Given {given}`c : γ, d : γ`, we have {lean}`c + d`.
-/

-- This theorem uses section variable γ. The moduledoc's `{given}` should not
-- interfere with how γ is used here.
theorem sectionVarClean (x y : γ) : x + y = x + y := rfl

open Lean in
#eval show TermElabM Unit from do
  let env ← getEnv
  let ci := env.constants.find? ``sectionVarClean |>.get!
  if ci.type.hasMVar then
    throwError "BUG: metavariable leaked into section theorem type: {ci.type}"

end VariableInteraction

section DecidableClassicalLeak
/-
If a `Decidable` instance from `givenInstance` in a moduledoc leaks into
the elaboration of a subsequent theorem, the theorem would pick up the leaked
`[Decidable p]` constraint instead of using `Classical.dec` from
`open Classical`. This would manifest as `Decidable p` appearing in the
theorem's type.
-/
variable (p : Prop)

/-!
Given {givenInstance}`Decidable p`, we can write {lean}`if p then True else False`.
-/

-- This theorem intentionally relies on Classical decidability, not a
-- `[Decidable p]` instance. If the moduledoc's `givenInstance` leaked,
-- the elaborator would use the leaked instance, adding `[Decidable p]` to
-- the theorem's type instead of using `Classical.dec`.
open Classical in
theorem classicalOnly : p ∨ ¬p := em p

-- The theorem's type must be `∀ (p : Prop), p ∨ ¬p` with no `Decidable`
-- parameter. If the constraint leaked, it would be
-- `∀ (p : Prop) [inst : Decidable p], p ∨ ¬p`.
/--
info: classicalOnly (p : Prop) : p ∨ ¬p
-/
#guard_msgs in
#check classicalOnly

-- Also verify programmatically
open Lean in
#eval show Elab.Term.TermElabM Unit from do
  let env ← getEnv
  let ci := env.constants.find? ``classicalOnly |>.get!
  let typeStr := toString (← Lean.Meta.MetaM.run' (Lean.PrettyPrinter.ppExpr ci.type))
  if typeStr.contains "Decidable" then
    throwError "BUG: Decidable constraint leaked from moduledoc into theorem: {typeStr}"

-- This is a more subtle case: a theorem that uses `decide`-like operations within its _body_ via
-- `open Classical`, where a leaked Decidable instance would silently change the theorem's
-- signature.
open Classical in
theorem classicalIte (q : Prop) : (if p then q else q) = q := by
  split <;> rfl

-- Should be `∀ (p : Prop) (q : Prop), ...` with no `Decidable p`.
/--
info: classicalIte (p q : Prop) : (if p then q else q) = q
-/
#guard_msgs in
#check classicalIte

end DecidableClassicalLeak

section DeclDocUnsolvedMeta
-- Unsolved `given` metavariables in declaration docs should also be errors.
/--
error: unresolved metavariable in `given` (type of variable `k`):
  ?m.3
-/
#guard_msgs in
/--
Given {given}`k`, we have {lean}`k`.
-/
def declDocUnsolved := ()

-- But a `given` whose type is resolved by a later `lean` should be fine.
/--
Given {given}`k`, we have {lean}`k + (1 : Nat)`.
-/
def declDocResolved := ()

end DeclDocUnsolvedMeta
