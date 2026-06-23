import Lean
/-!
# Synthetic tests of the dynamic docstrings for metavariables
-/

set_option linter.unusedVariables false

open Lean Elab Tactic

elab "#delab_docstrings " t:term : command => Command.runTermElabM fun _ => do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVars (postpone := .partial)
  logInfo m!"Expression: {e}"
  let { infos, .. } ← Meta.ppExprWithInfos e
  let infos := Array.qsort infos.toArray (lt := fun (p, _) (p', _) => p < p')
  for (p, info) in infos do
    if let .ofDelabTermInfo ti := info then
      if let some doc ← ti.docString? (← Meta.getPPContext) then
        let header ← Meta.withLCtx ti.lctx {} do
          addMessageContext m!"{ti.expr}"
        logInfo m!"{p}. {header}\n{doc}"

/-!
Natural metavariable.
-/
/--
info: Expression: ?m.2
---
info: 1. ?m.2
A metavariable representing an expression that should be solved for by unification during the elaboration process. They are created during elaboration as placeholders for implicit arguments and by `_` placeholder syntax.
-/
#guard_msgs in #delab_docstrings _

/-!
Synthetic opaque metavariable.
-/
/--
info: Expression: ?m.2
---
info: 1. ?m.2
A metavariable representing a tactic goal or an expression whose elaboration is still pending. They usually act like constants until they are completely solved for. They can be created using `?_` and `?n` synthetic placeholder syntax.
-/
#guard_msgs in #delab_docstrings ?_

/-!
A synthetic metavariable and a natural metavariable.
-/
/--
info: Expression: @default ?m.1 ?m.2
---
info: 5. ?m.2
A metavariable representing a typeclass instance whose synthesis is still pending. They can be solved for by unification during the elaboration process, but the inferred expression and the synthesized instance must be definitionally equal.
---
info: 17. ?m.1
A metavariable representing an expression that should be solved for by unification during the elaboration process. They are created during elaboration as placeholders for implicit arguments and by `_` placeholder syntax.
-/
#guard_msgs in set_option pp.explicit true in #delab_docstrings default

/-!
A delayed assignment pointing at a synthetic opaque metavariable.
-/
/--
info: Expression: fun n => ?foo
---
info: 5. ?foo
A metavariable representing a tactic goal or an expression whose elaboration is still pending. They usually act like constants until they are completely solved for. They can be created using `?_` and `?n` synthetic placeholder syntax.

This metavariable appears here via a *delayed assignment*. Substitution is delayed until the metavariable's value contains no metavariables, since all occurrences of the variables from its local context will need to be replaced with expressions that are valid in the current context.

Additional variable in this metavariable's local context: `n`
-/
#guard_msgs in #delab_docstrings fun (n : Nat) => ?foo

/-!
An assigned synthetic opaque metavariable that can't be instantiated due to a metavariable.
-/
/--
info: Expression: let f := fun b => ?_;
f true
---
info: 21. ?_
A metavariable representing a tactic goal or an expression whose elaboration is still pending. They usually act like constants until they are completely solved for. They can be created using `?_` and `?n` synthetic placeholder syntax.

This metavariable has been assigned, but it appears here via a *delayed assignment*. Substitution is delayed until the metavariable's value contains no metavariables, since all occurrences of the variables from its local context will need to be replaced with expressions that are valid in the current context. Substitution is awaiting assignment of the following metavariable: `?foo`

Additional variable in this metavariable's local context: `b`
-/
#guard_msgs in
set_option pp.mvars.anonymous false in
#delab_docstrings
  let f := fun (b : _) => if b then ?foo else true
  f true

elab "#delab_docstrings " t:term : tactic => withMainContext do
  let e ← Tactic.elabTerm t none
  logInfo m!"{e}"
  let { infos, .. } ← Meta.ppExprWithInfos e
  let infos := Array.qsort infos.toArray (lt := fun (p, _) (p', _) => p < p')
  for (p, info) in infos do
    if let .ofDelabTermInfo ti := info then
      if let some doc ← ti.docString? (← Meta.getPPContext) then
        let header ← Meta.withLCtx ti.lctx {} do
          addMessageContext m!"{ti.expr}"
        logInfo m!"{p}. {header}\n{doc}"

/-!
Metavariable shadowing. The `case'` tactic creates a new metavariablewith the same name.
This causes the original one to print as `?foo✝` and to report that the name is unreachable.
-/
/--
info: fun x => ?foo
---
info: 5. ?foo
A metavariable representing a tactic goal or an expression whose elaboration is still pending. They usually act like constants until they are completely solved for. They can be created using `?_` and `?n` synthetic placeholder syntax.

This metavariable appears here via a *delayed assignment*. Substitution is delayed until the metavariable's value contains no metavariables, since all occurrences of the variables from its local context will need to be replaced with expressions that are valid in the current context.

Additional variable in this metavariable's local context: `x`
---
info: fun x => ?foo✝
---
info: 5. ?foo✝
A metavariable representing a tactic goal or an expression whose elaboration is still pending. They usually act like constants until they are completely solved for. They can be created using `?_` and `?n` synthetic placeholder syntax.

This metavariable has a name but it is unreachable.

This metavariable has been assigned, but it appears here via a *delayed assignment*. Substitution is delayed until the metavariable's value contains no metavariables, since all occurrences of the variables from its local context will need to be replaced with expressions that are valid in the current context. Substitution is awaiting assignment of the following metavariable: `?foo`

Additional variable in this metavariable's local context: `x`
---
info: fun x => 0 + 1
-/
#guard_msgs in
example : True := by
  let f : Nat → Nat := fun x => ?foo
  #delab_docstrings value_of% f
  case' foo => refine ?_ + 1
  all_goals try #delab_docstrings value_of% f
  exact 0
  #delab_docstrings value_of% f
  trivial

/-!
Checking that metavariables report which variables are absent from their local contexts.
-/
/--
info: (?foo1, ?foo2, ?foo3)
---
info: 17. ?foo1
A metavariable representing a tactic goal or an expression whose elaboration is still pending. They usually act like constants until they are completely solved for. They can be created using `?_` and `?n` synthetic placeholder syntax.

Variables absent from this metavariable's local context: `x`, `y`, `z`
---
info: 21. ?foo3
A metavariable representing a tactic goal or an expression whose elaboration is still pending. They usually act like constants until they are completely solved for. They can be created using `?_` and `?n` synthetic placeholder syntax.

Variable absent from this metavariable's local context: `z`
---
info: 81. ?foo2
A metavariable representing a tactic goal or an expression whose elaboration is still pending. They usually act like constants until they are completely solved for. They can be created using `?_` and `?n` synthetic placeholder syntax.

Variables absent from this metavariable's local context: `y`, `z`
-/
#guard_msgs in
example : True := by
  let x : Nat := ?foo1
  let y : Nat := ?foo2
  let z : Nat := ?foo3
  #delab_docstrings (value_of% x, value_of% y, value_of% z)
  all_goals exact default
