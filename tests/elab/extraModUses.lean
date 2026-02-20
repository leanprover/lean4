module

import all Lean.ExtraModUses
public meta import Lean.Elab.Tactic.Basic

/-!
# Test for module dependencies described by ExtraModUses
-/

meta def resetExtraModUses : Lean.CoreM Unit := do
  Lean.modifyEnv (Lean.PersistentEnvExtension.setState Lean.extraModUses · ⟨[], ∅⟩)
  Lean.modifyEnv (Lean.PersistentEnvExtension.setState Lean.isExtraRevModUseExt · ⟨[], ()⟩)

meta def Lean.ExtraModUse.toImport (e : ExtraModUse) : Import :=
  { e with }

meta def showExtraModUses : Lean.CoreM Unit := do
  Lean.logInfo m!"Entries: {toString <| (Lean.extraModUses.getEntries (← Lean.getEnv)).map (·.toImport)}\n\
    Is rev mod use: {!(Lean.isExtraRevModUseExt.getEntries (← Lean.getEnv)).isEmpty}"

/-!
Test that the `resetExtraModUses` + `showExtraModUses` pair is working.
-/

#eval resetExtraModUses

/--
info: Entries: []
Is rev mod use: false
-/
#guard_msgs in #eval showExtraModUses

/-!
Notation being used in a command is recorded (here `«term_+_»` from Init.Notation)
-/

#eval resetExtraModUses

example := 3 + 3

/--
info: Entries: [import Init.Notation]
Is rev mod use: false
-/
#guard_msgs in #eval showExtraModUses

/-!
Declarations referenced using double-quoted names are recorded.
-/

#eval resetExtraModUses

def test1 := ``List.sum

/--
info: Entries: [import Init.Data.List.Basic]
Is rev mod use: false
-/
#guard_msgs in #eval showExtraModUses

/-!
`recommended_spelling` records a dependency.
-/

#eval resetExtraModUses

recommended_spelling "id" for "id" in [id]

/--
info: Entries: [import Init.Core, import Init.Prelude]
Is rev mod use: false
-/
#guard_msgs in #eval showExtraModUses

/-!
`syntax` records a dependency for the syntax category
(here Lean.Parser.Category.Term from Init.Notation).
-/

#eval resetExtraModUses

syntax "hi" : term

/--
info: Entries: [public import Init.Notation]
Is rev mod use: false
-/
#guard_msgs in #eval showExtraModUses

/-!
Term macro expansions are tracked (here `«term_+_»` from Init.Notation)
-/

macro "macro1" : term => `(3 + 3)

#eval resetExtraModUses

def test2 := macro1

/--
info: Entries: [import Init.Notation]
Is rev mod use: false
-/
#guard_msgs in #eval showExtraModUses

/-!
Tactic macro expansions are tracked (here `Lean.Parser.Tactic.tacticTrivial` from Init.Tactics)
-/

macro "macro2" : tactic => `(tactic| trivial)

#eval resetExtraModUses

public meta def test3 : True := by macro2

/--
info: Entries: [import Init.Tactics]
Is rev mod use: false
-/
#guard_msgs in #eval showExtraModUses

/-!
Tactic configuration structures are recorded.
-/

#eval resetExtraModUses

public def test4 : True := by simp +contextual

/--
info: Entries: [import Init.Tactics, meta import Init.MetaTypes]
Is rev mod use: false
-/
#guard_msgs in #eval showExtraModUses

/-!
`omega` introduces a dependency on `Init.Omega`.
-/

#eval resetExtraModUses

public def test5 : Eq 1 1 := by omega

/--
info: Entries: [import Init.Tactics, import Init.Omega]
Is rev mod use: false
-/
#guard_msgs in #eval showExtraModUses

/-!
References from `@[deprecated]` are tracked (here `Nat.add` from Init.Prelude)
-/

#eval resetExtraModUses

@[deprecated Nat.add "we decided to shorten the name" (since := "1010-10-10")]
def NaturalNumber.additionOperator := Nat.add

/--
info: Entries: [import Init.Notation, import Init.Prelude]
Is rev mod use: false
-/
#guard_msgs in #eval showExtraModUses

/-!
References from `@[grind]` are tracked (here `List.append` from Init.Prelude)
-/

#eval resetExtraModUses

attribute [grind =] List.append

/--
info: Entries: [import Init.Grind.Attr, public import Init.Prelude]
Is rev mod use: false
-/
#guard_msgs in #eval showExtraModUses

/-!
Local attribute applications are tracked as private.
-/

#eval resetExtraModUses

attribute [local grind =] List.append

/--
info: Entries: [import Init.Grind.Attr, import Init.Prelude]
Is rev mod use: false
-/
#guard_msgs in #eval showExtraModUses

/-!
Coercion instances are recorded as dependencies.
-/

#eval resetExtraModUses

public def test6 : Option Bool := false

/--
info: Entries: [import Init.Data.Option.Coe, import Init.Coe]
Is rev mod use: false
-/
#guard_msgs in #eval showExtraModUses

/-!
Simp theorems (especially defeq ones) are tracked (here `Nat.pow_succ` from Init.Data.Nat.Basic)
-/

#eval resetExtraModUses

def test7 : 2 ^ 8 = 256 := by simp [Nat.pow_succ]

/--
info: Entries: [import Init.Tactics, import Init.Data.Nat.Lemmas, import Init.Data.Nat.Basic, import Init.SimpLemmas, import Init.Notation]
Is rev mod use: false
-/
#guard_msgs in #eval showExtraModUses

/-!
`register_error_explanation` creates a dependency on `Lean.ErrorExplanation`.
-/

#eval resetExtraModUses

/-- This error never occurs. If you still get it, something went wrong, sorry -/
register_error_explanation lean.never {
  summary := "Not an error"
  sinceVersion := "never"
}

/--
info: Entries: [meta import Lean.ErrorExplanation]
Is rev mod use: false
-/
#guard_msgs in #eval showExtraModUses

/-!
The syntax node kind in `syntax` declarations get recorded as a `meta` dependency.
-/

#eval resetExtraModUses

syntax "test_me " Lean.Parser.Term.ident : term

/--
info: Entries: [public meta import Lean.Parser.Term, public import Init.Notation]
Is rev mod use: false
-/
#guard_msgs in #eval showExtraModUses

/-!
The categories in `syntax` declarations get recorded as a `meta` dependency.
-/

#eval resetExtraModUses

syntax "test_me " rcasesPat : term

/--
info: Entries: [public import Init.RCases, public import Init.Notation]
Is rev mod use: false
-/
#guard_msgs in #eval showExtraModUses

/-!
The quotation parser gets recorded as a `meta` dependency.
-/

#eval resetExtraModUses

def test8 : Lean.MacroM Lean.Syntax := `(Lean.Parser.Command.declaration| def a := 5)

/--
info: Entries: [import Init.Notation, import Init.Coe, meta import Lean.Parser.Command]
Is rev mod use: false
-/
#guard_msgs in #eval showExtraModUses

/-!
Elaboration attributes add dependency on the syntax node kind
(here `Lean.Parser.Tactic.done` from Init.Tactics).
-/

public meta def myElab : Lean.Elab.Tactic.Tactic := fun _ => pure ()

#eval resetExtraModUses

attribute [tactic Lean.Parser.Tactic.done] myElab

/--
info: Entries: [public import Init.Tactics]
Is rev mod use: false
-/
#guard_msgs in #eval showExtraModUses

/-!
Similarly with formatters...
-/

public meta def myFormatter : Lean.PrettyPrinter.Formatter := fun _ => pure ()

#eval resetExtraModUses

attribute [formatter Lean.Parser.Tactic.done] myFormatter

/--
info: Entries: [public import Init.Tactics]
Is rev mod use: false
-/
#guard_msgs in #eval showExtraModUses

/-!
... and parenthesizers
-/

public meta def myParenthesizer : Lean.PrettyPrinter.Parenthesizer := fun _ => pure ()

#eval resetExtraModUses

attribute [parenthesizer Lean.Parser.Tactic.done] myParenthesizer

/--
info: Entries: [public import Init.Tactics]
Is rev mod use: false
-/
#guard_msgs in #eval showExtraModUses
