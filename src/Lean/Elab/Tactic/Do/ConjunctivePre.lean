/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
import Init.BinderNameHint
public import Lean.Meta.Basic
import Lean.Meta.Match.MatcherInfo
public import Std.WP.Triple.Basic

/-!
# Conjunctive preconditions

`isConjunctiveInPosts` classifies the `@[spec]` theorems whose precondition `specPre Q` is
conjunctive in the schematic postcondition `Q`: `specPre a ⊓ specPre b ⊑ specPre (a ⊓ b)`. `vcgen`
applies such a spec directly and skips frame inference. The classification is an optimization: a
frameproc can recognize the same situations and decline to frame.

## Why no frame is needed

Apply the spec `specPre Q ⊑ wp x Q` to the goal `P ⊑ wp x Q`. The direct application emits the
single VC `(h₁) P ⊑ specPre Q`. A framed application with frame `F` needs `(h₂) P ⊑ F` and
`(h₃) P ⊓ F ⊑ specPre (fun _ => F)`, the spec-level `WP.Frames` obligation under the guard `P`. Its
conclusion follows from `h₁`, `h₂` and `h₃`:

    P ⊑ specPre Q ⊓ specPre (fun _ => F)    -- h₁, and h₂ with h₃
      ⊑ specPre (fun v => Q v ⊓ F)          -- conjunctivity
      ⊑ wp x (fun v => Q v ⊓ F)             -- the spec

So the direct application carries every admissible `F`. `WP.frames_of_conjunctive` is this
derivation with `specPre := wp x`.

## Syntactic detection

Every occurrence of `Q`/`E` in `specPre` must lie in a conjunctive context: the body of a `λ` or
`∀` with a `Q`-free binder type, an application `Q a⋯` with `Q`-free arguments, or a conjunctive
argument of a head in `conjunctiveArgs?`. A context applied to further `Q`-free arguments stays
conjunctive, because `(f ⊓ g) a = f a ⊓ g a`. For example:

    get       ↦  fun s => Q s s
    bind      ↦  wp x (fun a => wp (f a) Q E) E
    tryCatch  ↦  wp x Q (fun e => wp (h e) Q E, E.snd)

The `wp` arm assumes that the `wp` of the sub-program is conjunctive (`WPConjunctive`).

`conjunctiveArgs?` is a fixed table. An attribute on lemmas such as
`ite c a₁ b₁ ⊓ ite c a₂ b₂ ⊑ ite c (a₁ ⊓ a₂) (b₁ ⊓ b₂)` could extend it to user-defined heads,
reading the varying arguments as conjunctive and the shared ones as `Q`-free. Such a lemma would
have to state conjunctivity jointly in all varying arguments: `Or` is conjunctive in each argument
separately, but not jointly. There is no such attribute because the classification only saves
time: a spec with an unknown head goes through frame inference, and the frameproc can decline to
frame it, which yields the same VCs. An attribute pays off only once a user-defined head makes frame
inference measurably slow.

## Premises

A spec with a premise that mentions `Q`/`E` is not considered conjunctive, because its direct
application does not auto-frame. `vcgen` applies a spec at the current state `s` of the goal, and
this point frame `(· = s)` reaches the conclusion but not the premises. In

    (ht : P₁ ⊑ wp t Q) → (he : P₂ ⊑ wp e Q) → (if c then P₁ else P₂) ⊑ wp (ite c t e) Q

all facts about `s` must be guessed into `P₁` and `P₂`. The premise-free form
`(if c then wp t Q else wp e Q) ⊑ wp (ite c t e) Q` keeps both branches at `s`. A premise `Q = Q`
opts a spec out of the direct application.
-/

namespace Lean.Elab.Tactic.VCGen.SpecAttr

open Lean Meta Std.WP Lean.Order

/-- The precondition, program, postcondition and exception postcondition of a `Triple` or
`pre ⊑ wp …` conclusion. -/
private def specComponents? (concl : Expr) : Option (Expr × Expr × Expr × Expr) :=
  match_expr concl with
  | PartialOrder.rel _ _ pre rhs =>
    match_expr rhs with
    | wp _ _ _ _ _ _ _ prog post eposts => some (pre, prog, post, eposts)
    | _ => none
  | Triple _ _ _ _ _ _ x _ pre post eposts => some (pre, x, post, eposts)
  | _ => none

/-- Whether any metavariable from `mvarIds` occurs in `e`. -/
private def occursMVar (mvarIds : Array MVarId) (e : Expr) : Bool :=
  Option.isSome <| e.find? fun s => match s with | .mvar m => mvarIds.contains m | _ => false

/-- The arity of a conjunctive head and the positions of its conjunctive arguments. -/
private def conjunctiveArgs? (env : Environment) : Name → Option (Nat × List Nat)
  | ``Lean.Order.meet => some (4, [2, 3])
  | ``And => some (2, [0, 1])
  | ``Lean.Order.iInf => some (4, [3])
  | ``Lean.Order.himp => some (4, [3])
  | ``wp => some (10, [8, 9])
  | ``Prod.fst | ``Prod.snd => some (3, [2])
  | ``Prod.mk => some (4, [2, 3])
  | ``ite | ``dite => some (5, [3, 4])
  | ``cond => some (4, [2, 3])
  -- `binderNameHint v b e` is definitionally `e`.
  | ``binderNameHint => some (6, [5])
  | c => (getMatcherInfoCore? env c).map fun info =>
    (info.arity, List.range' info.getFirstAltPos info.numAlts)

/-- Whether every occurrence of `qs` in `e` lies in a conjunctive context. -/
private partial def isConjunctiveIn (env : Environment) (qs : Array MVarId) (e : Expr) : Bool :=
  if !occursMVar qs e then true else
  match e with
  | .mdata _ b => isConjunctiveIn env qs b
  | .lam _ dom body _ | .forallE _ dom body _ => !occursMVar qs dom && isConjunctiveIn env qs body
  | _ =>
    let args := e.getAppArgs
    match e.getAppFn with
    | .mvar m => qs.contains m && args.all (!occursMVar qs ·)
    | .const c _ =>
      match conjunctiveArgs? env c with
      | some (arity, conj) =>
        arity ≤ args.size && (List.range args.size).all fun i =>
          if conj.contains i then isConjunctiveIn env qs args[i]! else !occursMVar qs args[i]!
      | none => false
    | _ => false

/-- Whether the precondition of the spec `∀ binders, concl` is conjunctive in its schematic
postconditions. -/
public def isConjunctiveInPosts (concl : Expr) (binders : Array Expr) : MetaM Bool := do
  let some (pre, prog, post, eposts) := specComponents? concl | return false
  let qs := #[post, eposts].filterMap fun e => match e.eta with | .mvar q => some q | _ => none
  if qs.isEmpty then return false
  if occursMVar qs prog then return false
  for b in binders do
    if occursMVar qs (← inferType b) then return false
  return isConjunctiveIn (← getEnv) qs pre

end Lean.Elab.Tactic.VCGen.SpecAttr
