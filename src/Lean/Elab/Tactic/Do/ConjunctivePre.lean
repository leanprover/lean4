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
# Conjunctive preconditions: spec applications that need no frame

`isConjunctiveInPosts` classifies the `@[spec]` theorems whose precondition is conjunctive in the
schematic postconditions. `vcgen` applies such a spec directly, bypassing frame inference: any frame
the frame procedure could carry past the call is already carried by the direct application.

## Why no frame is needed

Consider applying a spec `P' ⊑ wp x Q'` to a goal `P ⊑ wp x Q` (`E` suppressed in this section). The
consequence rule yields two VCs, `P ⊑ P'` and `Q' ⊑ Q`. When the spec fixes a concrete `Q'`, the
post-VC may be unprovable: `Q` often needs information from `P` that `x` never touches, and `Q'`
knows nothing about it. The classical fix is framing: strengthen the spec to
`P' ⊓ F ⊑ wp x (fun v => Q' v ⊓ F)` and apply that instead, yielding

    (1) P ⊑ P' ⊓ F        (2) Q' ⊓ F ⊑ Q        (3) WP.Frames x F

where (3) makes the strengthening sound. The `F` must be specified: which part of `P` to carry is
hard to guess and undecidable in general, and guessing it is the frameproc's job.

For a spec with schematic post and a **conjunctive** precondition `P' := specPre Q'`,
`specPre a ⊓ specPre b ⊑ specPre (a ⊓ b)`, the framed application is never formed: unify
`Q' := Q` and emit the single VC

    (h₁) P ⊑ specPre Q

with `P` whole on the left-hand side and no `F` anywhere. What needs proof is that this loses
nothing against (1)–(3), and conjunctivity supplies it. Fix any `F` the framed route could have
used; its inputs were

    (h₂) P ⊑ F                       -- from (1)
    (h₃) F ⊑ specPre (fun _ => F)    -- (3), at the spec level

From (h₁)–(h₃), the framed application's conclusion is derived:

    P ⊑ specPre Q ⊓ specPre (fun _ => F)    -- (h₁); (h₂) chained with (h₃)
      ⊑ specPre (fun v => Q v ⊓ F)          -- conjunctivity
      ⊑ wp x (fun v => Q v ⊓ F)             -- the spec

So everything (1)–(3) could establish already follows from the emitted VC and the framed route's
own inputs: every admissible `F` is carried implicitly, none named, and no `WP.Frames` obligation
arises (`WP.Frames.of_conjunctive` is this derivation with `specPre := wp x`). A schematic post
alone does not suffice — a premise mentioning `Q` breaks the subsumption (see below). The
derivation only needs the composite `P ⊑ specPre (fun _ => F)`, which (h₂) and (h₃) imply: for
`get` it admits every `F` implied by `P`; for `modify f`, everything `P` guarantees about the
updated state. `P` is never split into a footprint and a frame.

## Syntactic detection

`isConjunctiveInPosts` checks a sufficient syntactic condition: every occurrence of the schematic
`Q`/`E` in `specPre` lies in a conjunctivity-preserving context — a `wp` post/exception-post, a
`⊓`/`∧`/`⨅` operand, a `⇨` consequent, an `EPost.Cons.head` projection, an application `Q a⋯`, or
under a `λ` — and none in a premise or the program. For instance:

    get   ↦  fun s => Q s s        throw  ↦  E.head err        bind  ↦  wp x (fun a => wp (f a) Q E) E

The `wp` context preserves conjunctivity only because the sub-program's `wp` is assumed conjunctive
(`WPConjunctive`), a per-program fact that every combinator preserves; a non-conjunctive leaf states
its precondition with an operator no arm matches and is rejected on its own terms.

Premises are rejected because of excess state arguments: `vcgen` applies a spec at the goal's
excess args, specializing the whole pre-VC to the current state `s`. That specialization is itself
a frame — the point-frame `(· = s)`, the strongest one — and it reaches only the conclusion's
precondition: a premise is a separate subgoal, an entailment over all states. A naive `ite` spec
shows the damage:

    (ht : P₁ ⊑ wp t Q) → (he : P₂ ⊑ wp e Q) → (if c then P₁ else P₂) ⊑ wp (if c then t else e) Q

everything known about the state before the `ite` must be guessed into `P₁`/`P₂` — the framing
problem all over again. The premise-free form
`(if c then wp t Q else wp e Q) ⊑ wp (if c then t else e) Q` keeps both branches at the current
state. A vacuous `Q = Q` premise thus opts a spec out of the direct path.

A middle ground exists for premise-style specs whose schematic pre `P'` heads every premise's pre
(`P' ⊓ guard`), as in

    (ht : ⦃P' ⊓ (c = True)⦄ t ⦃Q'⦄) → (he : ⦃P' ⊓ (c = False)⦄ e ⦃Q'⦄) → ⦃P'⦄ ite c t e ⦃Q'⦄

Applied to a goal with pre `P` at state `s`, instantiating `P' := (· = s) ⊓ (fun _ => P s)`
re-routes the point-frame through the premises: the conclusion VC trivializes and each premise
lands at the current state, losslessly. The analysis stays with the premise-free fragment.
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
