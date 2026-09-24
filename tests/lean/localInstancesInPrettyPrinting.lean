import Lean

open Lean Meta Elab PrettyPrinter Delaborator Syntax

class Bar where

syntax boolLit := &"true" <|> &"false"

/-- Syntax to embed our debugging logs in, in order to get them out of `Delab`. -/
syntax "⟪" ppLine
-- Whether `Bar` is synthesized
 &"synthBar" " := " boolLit "," ppLine
 -- Types of terms in the local context
 &"lctx" " := " "[" term,* "]" "," ppLine
 -- List of local instance names
 &"localInstanceNames" " := " "[" ident,* "]" ppLine
 "⟫" : term

/-- Syntax embedding debugging info for synthesizing `Bar`. -/
 def synthBarStxLog : MetaM Term := do
  let synthBar ← if (← synthInstance? (mkConst ``Bar)).isSome then `(boolLit|true) else `(boolLit|false)
  let lctx : TSepArray `term "," ← (← getLocalHyps).mapM fun e =>
    withOptions (·.setBool ``Lean.pp.notation false) do
      PrettyPrinter.delab <|← inferType e
  let localInstanceNames : TSepArray `ident "," :=
    (← getLocalInstances).map (mkIdent ·.className)
  `(⟪ synthBar := $synthBar,
    lctx := [$lctx,*],
    localInstanceNames := [$localInstanceNames,*]⟫)

/-- Dummy declaration to attach our `app_delab` to, to mimic circumstances in mathlib4#30266 -/
def foo (_ : Unit) : True := True.intro

@[app_delab foo]
partial def delabFoo : Delab := whenPPOption getPPNotation synthBarStxLog

variable [Bar]

-- Make sure the `[Bar]` instance is present in local instances and synthesis succeeds
#check foo ()

-- As a control for the above code, local instances are, as expected, correctly populated during term elaboration.
elab "test_elab%" : term => do
  logInfo m!"{← synthBarStxLog}"
  return mkConst ``Unit.unit

#check test_elab%
