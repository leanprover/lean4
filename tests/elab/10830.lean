import Lean

/-!
# Local instances should be available during delaboration
https://github.com/leanprover/lean4/issues/10830
-/

open Lean Meta Elab PrettyPrinter Delaborator Syntax

/-!
Example from issue.
-/
section Ex10830
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
def foo (_ : Nat) : True := True.intro

@[app_delab foo]
partial def delabFoo : Delab := whenPPOption getPPNotation synthBarStxLog

variable [Bar]

/-!
This used to print
```
info: ⟪
  synthBar := false,
  lctx := [Bar],
  localInstanceNames := []
  ⟫ : True
```
-/
/--
info: ⟪
  synthBar := true,
  lctx := [Bar],
  localInstanceNames := [Bar]
  ⟫ : True
-/
#guard_msgs in
#check foo 0

/-!
This matches what term elaboration sees in this context.
-/
elab "test_elab%" : term => do
  logInfo m!"{← synthBarStxLog}"
  return mkConst ``Unit.unit

/--
info: ⟪
  synthBar := true,
  lctx := [Bar],
  localInstanceNames := [Bar]
  ⟫
---
info: () : Unit
-/
#guard_msgs in
#check test_elab%
end Ex10830

/-!
Delaboration local instances exist under binders.
-/
/--
info: fun {α} [Inhabited α] [Bar] =>
  ⟪
    synthBar := true,
    lctx := [Type, Inhabited α, Bar],
    localInstanceNames := [Inhabited, Bar]
    ⟫ : ∀ {α : Type} [Inhabited α] [Bar], True
-/
#guard_msgs in
#check fun {α : Type} [Inhabited α] [Bar] => foo 0

/-!
Local instances exist for goals.
-/
/--
trace: inst✝ : Bar
⊢ ⟪
      synthBar := true,
      lctx := [Bar],
      localInstanceNames := [Bar]
      ⟫ =
    trivial
-/
#guard_msgs in
set_option pp.proofs true in
example [Bar] : foo 0 = trivial := by
  trace_state
  trivial
