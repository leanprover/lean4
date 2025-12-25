/-
Copyright (c) 2020 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Lean.Meta.Tactic.Simp.Main
import Lean.Linter.OtherLinter.Basic

-- import Std.Util.LibraryNote -- Not yet ported

open Lean Meta

namespace Std.Tactic.Lint

/-!
# Linter for simplification lemmas

This files defines several linters that prevent common mistakes when declaring simp lemmas:

 * `simpNF` checks that the left-hand side of a simp lemma is not simplified by a different lemma.
 * `simpVarHead` checks that the head symbol of the left-hand side is not a variable.
 * `simpComm` checks that commutativity lemmas are not marked as simplification lemmas.
-/

/-- The data associated to a simp theorem. -/
structure SimpTheoremInfo where
  /-- The hypotheses of the theorem -/
  hyps : Array Expr
  /-- True if this is a conditional rewrite rule -/
  isConditional : Bool
  /-- The thing to replace -/
  lhs : Expr
  /-- The result of replacement -/
  rhs : Expr

/-- Given the list of hypotheses, is this a conditional rewrite rule? -/
def isConditionalHyps (lhs : Expr) : List Expr → MetaM Bool
  | [] => pure false
  | h :: hs => do
    let ldecl ← getFVarLocalDecl h
    if !ldecl.binderInfo.isInstImplicit
        && !(← hs.anyM fun h' =>
          return (← inferType h').consumeTypeAnnotations.containsFVar h.fvarId!)
        && !lhs.containsFVar h.fvarId! then
      return true
    isConditionalHyps lhs hs

-- FIXME
-- open private preprocess from Lean.Meta.Tactic.Simp.SimpTheorems in
/-- Runs the continuation on all the simp theorems encoded in the given type. -/
def withSimpTheoremInfos (ty : Expr) (k : SimpTheoremInfo → MetaM α) : MetaM (Array α) :=
  withReducible do
    sorry
    -- let e ← preprocess (← mkSorry ty true) ty (inv := false) (isGlobal := true)
    -- e.toArray.mapM fun (_, ty') => do
    --   forallTelescopeReducing ty' fun hyps eq => do
    --     let some (_, lhs, rhs) := eq.eq? | throwError "not an equality {eq}"
    --     let isConditional ← isConditionalHyps lhs hyps.toList
    --     k { hyps, lhs, rhs, isConditional }

/-- Checks whether two expressions are equal for the simplifier. That is,
they are reducibly-definitional equal, and they have the same head symbol. -/
def isSimpEq (a b : Expr) (whnfFirst := true) : MetaM Bool := withReducible do
  let a ← if whnfFirst then whnf a else pure a
  let b ← if whnfFirst then whnf b else pure b
  if a.getAppFn.constName? != b.getAppFn.constName? then return false
  isDefEq a b

/-- Constructs a message from all the simp theorems encoded in the given type. -/
def checkAllSimpTheoremInfos (ty : Expr) (k : SimpTheoremInfo → MetaM (Option MessageData)) :
    MetaM (Option MessageData) := do
  let errors :=
    (← withSimpTheoremInfos ty fun i => do (← k i).mapM addMessageContextFull).filterMap id
  if errors.isEmpty then
    return none
  return MessageData.joinSep errors.toList Format.line

/-- Returns true if this is a `@[simp]` declaration. -/
def isSimpTheorem (declName : Name) : MetaM Bool := do
  pure $ (← getSimpTheorems).lemmaNames.contains (.decl declName)

open Lean.Meta.DiscrTree in
/-- Returns the list of elements in the discrimination tree. -/
partial def _root_.Lean.Meta.DiscrTree.elements (d : DiscrTree α) : Array α :=
  d.root.foldl (init := #[]) fun arr _ => trieElements arr
where
  /-- Returns the list of elements in the trie. -/
  trieElements (arr)
  | Trie.node vs children =>
    children.foldl (init := arr ++ vs) fun arr (_, child) => trieElements arr child

open Std

/-- Add message `msg` to any errors thrown inside `k`. -/
def decorateError (msg : MessageData) (k : MetaM α) : MetaM α := do
  try k catch e => throw (.error e.getRef m!"{msg}\n{e.toMessageData}")

/-- Render the list of simp lemmas. -/
def formatLemmas (usedSimps : Simp.UsedSimps) : MetaM MessageData := do
  let mut args := #[]
  let env ← getEnv
  for (thm, _) in usedSimps.toArray.qsort (·.2 < ·.2) do
    if let .decl declName := thm then
      if env.contains declName && declName != ``eq_self then
        args := args.push (← mkConstWithFreshMVarLevels declName)
  return m!"simp only {args.toList}"

/-- A linter for simp lemmas whose lhs is not in simp-normal form, and which hence never fire. -/
@[std_linter] def simpNF : Linter where
  noErrorsFound := "All left-hand sides of simp lemmas are in simp-normal form."
  errorsFound := "SOME SIMP LEMMAS ARE NOT IN SIMP-NORMAL FORM.
see note [simp-normal form] for tips how to debug this.
https://leanprover-community.github.io/mathlib_docs/notes.html#simp-normal%20form"
  test := fun declName => do
    unless ← isSimpTheorem declName do return none
    let ctx := { ← Simp.Context.mkDefault with config.decide := false }
    checkAllSimpTheoremInfos (← getConstInfo declName).type fun {lhs, rhs, isConditional, ..} => do
      let ({ expr := lhs', proof? := prf1, .. }, prf1Lems) ←
        decorateError "simplify fails on left-hand side:" <| simp lhs ctx
      if prf1Lems.contains (.decl declName) then return none
      let ({ expr := rhs', .. }, used_lemmas) ←
        decorateError "simplify fails on right-hand side:" <| simp rhs ctx (usedSimps := prf1Lems)
      let lhs'EqRhs' ← isSimpEq lhs' rhs' (whnfFirst := false)
      let lhsInNF ← isSimpEq lhs' lhs
      if lhs'EqRhs' then
        if prf1.isNone then return none -- TODO: FP rewriting foo.eq_2 using `simp only [foo]`
        return m!"simp can prove this:
  by {← formatLemmas used_lemmas}
One of the lemmas above could be a duplicate.
If that's not the case try reordering lemmas or adding @[priority].
"
      else if ¬ lhsInNF then
        return m!"Left-hand side simplifies from
  {lhs}
to
  {lhs'}
using
  {← formatLemmas prf1Lems}
Try to change the left-hand side to the simplified term!
"
      else if !isConditional && lhs == lhs' then
        return m!"Left-hand side does not simplify, when using the simp lemma on itself.
This usually means that it will never apply.
"
      else
        return none

-- We haven't yet ported `Std.Util.LibraryNote`
-- (which is incomplete in any case),
-- so this is just a normal comment.
-- library_note "simp-normal form"
/-
This note gives you some tips to debug any errors that the simp-normal form linter raises.

The reason that a lemma was considered faulty is because its left-hand side is not in simp-normal
form.
These lemmas are hence never used by the simplifier.

This linter gives you a list of other simp lemmas: look at them!

Here are some tips depending on the error raised by the linter:

  1. 'the left-hand side reduces to XYZ':
     you should probably use XYZ as the left-hand side.

  2. 'simp can prove this':
     This typically means that lemma is a duplicate, or is shadowed by another lemma:

     2a. Always put more general lemmas after specific ones:
      ```
      @[simp] lemma zero_add_zero : 0 + 0 = 0 := rfl
      @[simp] lemma add_zero : x + 0 = x := rfl
      ```

      And not the other way around!  The simplifier always picks the last matching lemma.

     2b. You can also use `@[priority]` instead of moving simp-lemmas around in the file.

      Tip: the default priority is 1000.
      Use `@[priority 1100]` instead of moving a lemma down,
      and `@[priority 900]` instead of moving a lemma up.

     2c. Conditional simp lemmas are tried last. If they are shadowed
         just remove the `simp` attribute.

     2d. If two lemmas are duplicates, the linter will complain about the first one.
         Try to fix the second one instead!
         (You can find it among the other simp lemmas the linter prints out!)

  3. 'try_for tactic failed, timeout':
     This typically means that there is a loop of simp lemmas.
     Try to apply squeeze_simp to the right-hand side (removing this lemma from the simp set) to see
     what lemmas might be causing the loop.

     Another trick is to `set_option trace.simplify.rewrite true` and
     then apply `try_for 10000 { simp }` to the right-hand side.  You will
     see a periodic sequence of lemma applications in the trace message.
-/

/--
A linter for simp lemmas whose lhs has a variable as head symbol,
and which hence never fire.
-/
@[std_linter] def simpVarHead : Linter where
  noErrorsFound :=
    "No left-hand sides of a simp lemma has a variable as head symbol."
  errorsFound := "LEFT-HAND SIDE HAS VARIABLE AS HEAD SYMBOL.
Some simp lemmas have a variable as head symbol of the left-hand side (after whnfR):"
  test := fun declName => do
    unless ← isSimpTheorem declName do return none
    checkAllSimpTheoremInfos (← getConstInfo declName).type fun {lhs, ..} => do
    let lhs ← whnfR lhs
    let headSym := lhs.getAppFn
    unless headSym.isFVar do return none
    return m!"Left-hand side has variable as head symbol: {headSym}"

private def Expr.eqOrIff? : Expr → Option (Expr × Expr)
  | .app (.app (.app (.const ``Eq _) _) lhs) rhs
  | .app (.app (.const ``Iff _) lhs) rhs
    => (lhs, rhs)
  | _ => none

/-- A linter for commutativity lemmas that are marked simp. -/
@[std_linter] def simpComm : Linter where
  noErrorsFound := "No commutativity lemma is marked simp."
  errorsFound := "COMMUTATIVITY LEMMA IS SIMP.
Some commutativity lemmas are simp lemmas:"
  test := fun declName => withReducible do
    unless ← isSimpTheorem declName do return none
    let ty := (← getConstInfo declName).type
    forallTelescopeReducing ty fun _ ty' => do
    let some (lhs, rhs) := ty'.eqOrIff? | return none
    unless lhs.getAppFn.constName? == rhs.getAppFn.constName? do return none
    let (_, _, ty') ← forallMetaTelescopeReducing ty
    let some (lhs', rhs') := ty'.eqOrIff? | return none
    unless ← isDefEq rhs lhs' do return none
    unless ← withNewMCtxDepth (isDefEq rhs lhs') do return none
    -- make sure that the discrimination tree will actually find this match (see #69)
    if (← (← DiscrTree.empty.insert rhs () simpDtConfig).getMatch lhs' simpDtConfig).isEmpty then
      return none
    -- ensure that the second application makes progress:
    if ← isDefEq lhs' rhs' then return none
    pure m!"should not be marked simp"
