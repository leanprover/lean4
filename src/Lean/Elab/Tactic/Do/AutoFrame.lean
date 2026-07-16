/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Meta.Basic
public import Std.Internal.Do.Triple.Basic

/-!
# Conjunctive preconditions: a syntactic sufficient condition for automatic framing

Recall what framing a call `x` asks of us. To carry a frame `F` past `x` — `x` runs without disturbing
`F` — we must discharge `F ⊓ P ⊑ wp x (fun a => F ⊓ Q a)`: `F` holds beforehand and survives into every
postcondition. The `F` we supply has to be a frame `wp x` admits, and we want the *strongest* such one.
We cannot compute it — guessing the strongest frame a `wp` admits is undecidable in general.

The point of this module: for a **conjunctive** `wp x` we never name `F`. It stays a symbolic stand-in
for "the strongest admissible frame". Reading the postcondition as `Q ⊓ F` — the real postcondition met
with the abstract frame — conjunctivity `wp x Q ⊓ wp x F ⊑ wp x (Q ⊓ F)` turns the framed goal
`F ⊓ P ⊑ wp x (Q ⊓ F)` into

    P ⊑ wp x Q          -- the plain, unframed goal
    F ⊓ P ⊑ wp x F      -- the frame side-condition: `x` preserves `F`

with `F` never instantiated. It comes from nowhere.

A `@[spec]` `specPre Q E ⊑ wp prog Q E` inherits this the moment `specPre`, read as a function of its
schematic postconditions `Q`/`E`, is itself conjunctive: `specPre a ⊓ specPre b ⊑ specPre (a ⊓ b)`. Then
applying the spec directly leaves `goalPre ⊑ specPre Q E`, and the same split carries any frame sitting
in `goalPre`. Such preconditions, as functions of `Q`/`E`, look like:

    get    ↦  fun s => Q s s
    throw  ↦  E.head err
    bind   ↦  wp x (fun a => wp (f a) Q E) E

`isConjunctiveInPosts` decides a **sufficient syntactic condition** for `specPre` being conjunctive:
every occurrence of `Q`/`E` sits in a conjunctive context — a `wp` postcondition or
exception-postcondition argument, a `⊓`/`∧`/`⨅` operand, a `⇨` consequent, an `EPost.Cons.head`
projection, applied at a tail, or under a `λ`. An occurrence of `Q`/`E` in a premise is rejected; this
is the opt-out, so a spec forces rejection with a trivial `Q = Q` premise. See
`WP.Frames.of_conjunctive`.

The `wp` arm **assumes** the program's `wp` is conjunctive: `wp x (Q₁ ⊓ Q₂) (E₁ ⊓ E₂) = wp x Q₁ E₁ ⊓ wp
x Q₂ E₂` — a per-program semantic fact, not visible in the syntax, preserved by every combinator. So
recursing through a `wp` defers the frame decision to that sub-program; a genuinely non-conjunctive
leaf states its precondition with a non-conjunctive operator that no arm matches, and is rejected on
its own terms.
-/

namespace Lean.Elab.Tactic.Do.Internal.SpecAttr

open Lean Meta Std.Internal.Do Lean.Order

/-- The precondition, program, postcondition, and exception postcondition of a spec conclusion in
either `Triple` or `pre ⊑ wp …` shape. -/
private def specComponents? (concl : Expr) : Option (Expr × Expr × Expr × Expr) :=
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
each occurs only in conjunctive contexts, and in no premise nor in the program. The `binders` are the
spec's `∀`-telescoped parameters and premises. -/
public def isConjunctiveInPosts (concl : Expr) (binders : Array Expr) : MetaM Bool := do
  let some (pre, prog, post, epost) := specComponents? concl | return false
  let qs := #[post, epost].filterMap fun e => match e.eta with | .mvar q => some q | _ => none
  if qs.isEmpty then return false
  if occursMVar qs prog then return false
  -- A premise mentioning `Q`/`E` rejects the spec — this is the `Q = Q` opt-out. Incomplete: a
  -- premise that only pins a postcondition, e.g. `E = ⊥`, is rejected too.
  for b in binders do
    if occursMVar qs (← inferType b) then return false
  return isConjunctiveIn qs pre

end Lean.Elab.Tactic.Do.Internal.SpecAttr
