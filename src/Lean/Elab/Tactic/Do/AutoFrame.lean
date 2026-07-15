/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Meta.Basic
public import Std.Internal.Do.Triple.Basic

public section

/-!
# Conjunctive preconditions: a syntactic sufficient condition for automatic framing

`vcgen` may apply a `@[spec]` `specPre Q E ⊑ wp prog Q E` directly, without any frame machinery, and
still carry an arbitrary frame `F` through the call, exactly when the precondition, read as a function
of its schematic postconditions `Q`/`E`, is **conjunctive**: `specPre a ⊓ specPre b ⊑ specPre (a ⊓ b)`.
Reinstantiating `Q ↦ Q ⊓ F` then splits the frame off — `specPre F ⊓ specPre Q ⊑ specPre (F ⊓ Q)` — so
`specPre F` becomes a side goal and `goalPre` stays on the left of the residual entailment. That is the
automatic-framing quality this module detects.

`isConjunctiveInPosts` decides a **sufficient syntactic condition** for it: every occurrence of `Q`/`E`
in the precondition sits in a conjunctive context — a `wp` postcondition or exception-postcondition
argument, a `⊓`/`∧`/`⨅` operand, a `⇨` consequent, an `EPost.Cons.head` projection, applied at a tail,
or under a `λ` — and `Q`/`E` occur in no premise nor in the program. Conjunctive contexts compose and
combine under `⊓`, so a precondition built only from these is conjunctive, hence the spec auto-frames.

The `wp` argument **assumes** the program's `wp` is conjunctive (`wp x (Q₁ ⊓ Q₂) E = wp x Q₁ E ⊓ wp x
Q₂ E`). Conjunctivity is a per-program semantic fact, not visible in the spec's syntax, and it is
preserved by every combinator, so recursing through a `wp` defers the frame decision to that
sub-program: a leaf whose `wp` is genuinely non-conjunctive states its precondition with a
non-conjunctive operator, which no arm matches, and is rejected on its own terms. A spec can force
rejection with a trivial `Q = Q` premise.
-/

namespace Lean.Elab.Tactic.Do.Internal.SpecAttr

open Lean Meta Std.Internal.Do Lean.Order

/-- The precondition, program, postcondition, and exception postcondition of a spec conclusion in
either `Triple` or `pre ⊑ wp …` shape. -/
def specComponents? (concl : Expr) : Option (Expr × Expr × Expr × Expr) :=
  match_expr concl with
  | PartialOrder.rel _ _ pre rhs =>
    match_expr rhs with
    | wp _ _ _ _ _ _ _ prog post epost => some (pre, prog, post, epost)
    | _ => none
  | Triple _ _ _ _ _ _ x _ pre post epost => some (pre, x, post, epost)
  | _ => none

/-- Whether any metavariable from `mvarIds` occurs in `e`. -/
private def occursMVar (mvarIds : Array MVarId) (e : Expr) : Bool :=
  Option.isSome <| e.find? fun s => match s with | .mvar m => mvarIds.contains m | _ => false

/-- Whether `e` is conjunctive in the metavariables `qs`, as a sufficient syntactic condition: every
occurrence of a `qs` metavariable lies in a conjunctive context — a `wp` postcondition or
exception-postcondition argument (assuming the program's `wp` is conjunctive), a `⊓`/`∧`/`⨅` operand,
a `⇨` consequent, an `EPost.Cons.head` projection, applied at a tail, or under a `λ`. -/
private partial def isConjunctiveIn (qs : Array MVarId) (e : Expr) : Bool :=
  if !occursMVar qs e then true else
  match e with
  | .mdata _ b => isConjunctiveIn qs b
  | .lam _ dom body _ => !occursMVar qs dom && isConjunctiveIn qs body
  | _ =>
    match e.getAppFn with
    | .mvar m => qs.contains m && e.getAppArgs.all (!occursMVar qs ·)
    | .const ``EPost.Cons.head _ =>
      -- `EPost.Cons.head` is a `⊓`-morphism (`EPost.Cons.head_meet`); its exception-stack argument
      -- stays in a `⊓`-context, the rest (types and the applied exception) must be `qs`-free.
      let args := e.getAppArgs
      match args[2]? with
      | some s => isConjunctiveIn qs s && (List.range args.size).all fun i => i == 2 || !occursMVar qs args[i]!
      | none => false
    | _ =>
      match_expr e with
      | Lean.Order.meet _ _ a b => isConjunctiveIn qs a && isConjunctiveIn qs b
      | Lean.Order.iInf _ _ _ f => isConjunctiveIn qs f
      | And a b => isConjunctiveIn qs a && isConjunctiveIn qs b
      | Lean.Order.himp _ _ a b => !occursMVar qs a && isConjunctiveIn qs b
      | wp _ _ _ _ _ _ _ prog post epost =>
        !occursMVar qs prog && isConjunctiveIn qs post && isConjunctiveIn qs epost
      | _ => false

/-- Whether the spec's precondition is conjunctive in its schematic postconditions (`Q` and/or `E`):
each occurs only where the precondition is conjunctive, and in no premise nor in the program. Such a
spec carries any frame when applied directly. The `binders` are the spec's `∀`-telescoped parameters
and premises. -/
def isConjunctiveInPosts (concl : Expr) (binders : Array Expr) : MetaM Bool := do
  let some (pre, prog, post, epost) := specComponents? concl | return false
  let qs := #[post, epost].filterMap fun e => match e.eta with | .mvar q => some q | _ => none
  if qs.isEmpty then return false
  if occursMVar qs prog then return false
  for b in binders do
    if occursMVar qs (← inferType b) then return false
  unless occursMVar qs pre do return false
  return isConjunctiveIn qs pre

end Lean.Elab.Tactic.Do.Internal.SpecAttr
