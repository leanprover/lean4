import Lean

/-!
Tests the `@[fmt_provider]` attribute, which registers `Lean.Fmt.FmtProvider`s downstream of core.
Checks that registered providers are consulted, that their priority orders them both against each
other and against the providers built into core, and that the attribute rejects ill-typed and
non-global applications.
-/

open Lean Lean.Fmt

/-- The declaration name of the formatter that the registered providers resolve `kind` to. -/
def resolve (kind : SyntaxNodeKind) : CoreM Name := do
  let env ← getEnv
  let opts ← getOptions
  let some (declName, _) := getFmtProviders env |>.findSome? (·.provider env opts kind)
    | throwError "No `FmtProvider` claims `{kind}`"
  return declName

/-- Only parses an atom, so core's `derivedAtomicFmtProvider` (priority 400) claims it. -/
syntax (name := atomicTestSyntax) "atomicTest" : term

/-- Claimed by `fmtTestSyntax` below, which is registered with `@[fmt]` (priority 1000). -/
syntax (name := formattedTestSyntax) "formattedTest" : term

@[fmt formattedTestSyntax]
def fmtTestSyntax : Fmt := fmtAtomic

/-- info: `Lean.Fmt.fmtAtomic -/
#guard_msgs in
#eval resolve `atomicTestSyntax

/-- info: `fmtTestSyntax -/
#guard_msgs in
#eval resolve `formattedTestSyntax

/-- error: No `FmtProvider` claims `unclaimedTestKind` -/
#guard_msgs in
#eval resolve `unclaimedTestKind

/-- Neither claimed by a formatter of its own nor derived from its `ParserDescr`. -/
syntax (name := unformattedTestSyntax) "unformattedTest" "[" term "]" : term

macro_rules
  | `(unformattedTest [ $x ]) => `($x)

set_option linter.fmt.missing true

/--
warning: no auto-formatter registered for syntax kind unformattedTestSyntax

Note: This linter can be disabled with `set_option linter.fmt.missing false`
-/
#guard_msgs in
example : Nat := unformattedTest [ 1 ]

/-- Claims every syntax node kind, so its priority alone decides what it shadows. -/
def catchAllProvider : FmtProvider := fun _ _ _ => some (`catchAllProvider, fmtAtomic)

attribute [fmt_provider 500] catchAllProvider

-- The formatter dispatch consults the registered provider, so the linter goes quiet.

#guard_msgs in
example : Nat := unformattedTest [ 1 ]

-- Sits above core's derived atomic provider (400), but below `@[fmt]` (1000).

/-- info: `catchAllProvider -/
#guard_msgs in
#eval resolve `atomicTestSyntax

/-- info: `fmtTestSyntax -/
#guard_msgs in
#eval resolve `formattedTestSyntax

/-- info: `catchAllProvider -/
#guard_msgs in
#eval resolve `unclaimedTestKind

/-- Claims a single kind, at a priority above every provider in core. -/
def claimedKindProvider : FmtProvider := fun _ _ kind => do
  guard <| kind == `formattedTestSyntax
  return (`claimedKindProvider, fmtAtomic)

attribute [fmt_provider 2000] claimedKindProvider

/-- info: `claimedKindProvider -/
#guard_msgs in
#eval resolve `formattedTestSyntax

/-- Registered at the same priority as `claimedKindProvider`, but after it. -/
def laterCatchAllProvider : FmtProvider := fun _ _ _ => some (`laterCatchAllProvider, fmtAtomic)

attribute [fmt_provider 2000] laterCatchAllProvider

-- Providers of equal priority are consulted in registration order, so the earlier one still wins
-- for the kind it claims.

/-- info: `claimedKindProvider -/
#guard_msgs in
#eval resolve `formattedTestSyntax

/-- info: `laterCatchAllProvider -/
#guard_msgs in
#eval resolve `atomicTestSyntax

/-- The default priority is `1000`, which ties with the formatters registered with `@[fmt]`. -/
def defaultPriorityProvider : FmtProvider := fun _ _ _ => some (`defaultPriorityProvider, fmtAtomic)

/--
error: Invalid attribute scope: Attribute `[fmt_provider]` must be global, not `local`
-/
#guard_msgs in
attribute [local fmt_provider] defaultPriorityProvider

def notAProvider : Nat := 0

/--
error: Cannot add attribute `[fmt_provider]`: Declaration `notAProvider` has type
  Nat
but `[fmt_provider]` can only be added to declarations of type
  FmtProvider
-/
#guard_msgs in
attribute [fmt_provider] notAProvider
