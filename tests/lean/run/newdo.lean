import Lean
import Lean.Parser.Term.Basic
import Lean.Elab.Tactic.Do.LetElim
import Std.Tactic.Do
import Lean.Elab.Do.Control
import Lean.Elab.BuiltinDo
import Lean.Parser.Term
import Init.NotationExtra
import Init.Control.Basic
import Std.Data.Iterators.Lemmas.Combinators.Monadic.Zip
import Lake.Util.JsonObject
import Lean.Elab.Tactic.Do.ProofMode.MGoal
import Lean.Elab.Tactic.Do.ProofMode.Pure
import Init.Omega

open Lean Parser Meta Elab Do

set_option linter.unusedVariables false

set_option pp.all true in
@[inline]
def ForIn.forInInv {m} {ρ : Type u} {α : Type v} [ForIn m ρ α] {β}
    (xs : ρ) (s : β) (f : α → β → m (ForInStep β))
    [Monad m] [inst : ForIn.{u,v,v,v} Id ρ α] {ps} [Std.Do.WP m ps] (inv : Std.Do.Invariant (inst.toList xs) β ps) : m β :=
  forIn xs s f

meta def doInvariant := leading_parser
  "invariant " >> withPosition (
    ppGroup (many1 (ppSpace >> termParser argPrec) >> unicodeSymbol " ↦" " =>" (preserveForPP := true)) >> ppSpace >> withForbidden "do" termParser)
syntax (name := doForInvariant) "for " Term.doForDecl ppSpace doInvariant "do " doSeq : doElem

namespace Do

section Backtrack

/--
Execute `x?`, but backtrack state if result is `none` or an exception was thrown.
-/
def commitWhenSome? [Monad m] [MonadBacktrack s m] [MonadExcept ε m] (x? : m (Option α)) : m (Option α) := do
  let s ← saveState
  try
    match (← x?) with
    | some a => return some a
    | none   =>
      restoreState s
      return none
  catch ex =>
    restoreState s
    throw ex

def commitWhenSomeNoEx? {m s α ε} [Monad m] [MonadBacktrack s m] [MonadExcept ε m] (x? : m (Option α)) : m (Option α) := do
  let mut a := 0
  try
    a := 1
    commitWhenSome? x?
  catch _ =>
    return none

end Backtrack

section Array

set_option trace.Elab.do.match true in
@[inline, expose]
def findSomeM? {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : α → m (Option β)) (as : Array α) : m (Option β) := do
  for a in as do
    match (← f a) with
    | some b => return some b
    | _      => pure ⟨⟩
  return none

def Array.mapM' [Monad m] (f : α → m β) (as : Array α) : m { bs : Array β // bs.size = as.size } :=
  go 0 ⟨Array.mkEmpty as.size, rfl⟩ (by simp)
where
  go (i : Nat) (acc : { bs : Array β // bs.size = i }) (hle : i ≤ as.size) : m { bs : Array β // bs.size = as.size } := do
    if h : i = as.size then
      return h ▸ acc
    else
      have hlt : i < as.size := Nat.lt_of_le_of_ne hle h
      let b ← f as[i]
      go (i+1) ⟨acc.val.push b, by simp [acc.property]⟩ hlt
  termination_by as.size - i
  decreasing_by decreasing_trivial_pre_omega

public def filterPairsM {m} [Monad m] {α} (a : Array α) (f : α → α → m (Bool × Bool)) :
    m (Array α) := do
  let mut removed := Array.replicate a.size false
  let mut numRemoved := 0
  for h1 : i in *...a.size do for h2 : j in (i+1)...a.size do
    unless removed[i]! || removed[j]! do
      let xi := a[i]
      let xj := a[j]
      let (keepi, keepj) ← f xi xj
      unless keepi do
        numRemoved := numRemoved + 1
        removed := removed.set! i true
      unless keepj do
        numRemoved := numRemoved + 1
        removed := removed.set! j true
  let mut a' := Array.mkEmpty numRemoved
  for h : i in *...a.size do
    unless removed[i]! do
      a' := a'.push a[i]
  return a'

end Array

section Tactic

private meta def expandIfThenElse'
    (ifTk thenTk elseTk pos neg : Syntax)
    (mkIf : Term → Term → MacroM Term) : MacroM (TSyntax `term) := do
  let mkCase tk holeOrTacticSeq mkName : MacroM (TSyntax `term) := do
    let hole ← withFreshMacroScope mkName
    if holeOrTacticSeq.isOfKind `Lean.Parser.Term.syntheticHole then
      pure hole
    else
      pure hole
  mkCase thenTk pos `(?pos)

end Tactic

section Blah

def f1 : ExceptT String (StateT Nat Id) Nat := do
  modify (· + 1)
  get

def f2 (x : Nat) : ExceptT String (StateT Nat Id) Nat := do
  modify (· + x)
  get

def f9 (xs : List Nat) : IO (List Nat) := do
return xs
return xs -- warn unreachable

example (declName : Name) (x : Bool) (f : String → MetaM Bool) : MetaM Unit := do
  let res ← match x with | _ => throwError m!"`{.ofConstName declName}` has no docstring"
  let _ ← f res
  throwError "No metadata satisfied the predicate"

set_option trace.Elab.do true in
def logErrorNames (x : MetaM Unit) : MetaM Unit := do
  Core.setMessageLog {}
  x
  let log ← Core.getMessageLog
  let mut newLog := {}
  for msg in log.toArray do
    newLog := newLog.add <|
      if let some errorName := msg.errorName? then
        { msg with data := m!"({errorName}) " ++ msg.data }
      else
        msg
  Core.setMessageLog newLog

open Std IterM in
example [Monad m] [Iterator α₁ m β₁] [Iterator α₂ m β₂]
    {it₁ : IterM (α := α₁) m β₁}
    {memo : Option { out : β₁ //
        ∃ it : IterM (α := α₁) m β₁, it.IsPlausibleOutput out }}
    {it₂ : IterM (α := α₂) m β₂} :
    (Intermediate.zip it₁ memo it₂).step = (do
      match memo with
      | none =>
        match (← it₁.step).inflate with
        | .yield it₁' out hp =>
          pure <| .deflate <| .skip (Intermediate.zip it₁' (some ⟨out, _, _, hp⟩) it₂)
            (.yieldLeft rfl hp)
        | .skip it₁' hp =>
          pure <| .deflate <| .skip (Intermediate.zip it₁' none it₂)
            (.skipLeft rfl hp)
        | .done hp =>
          pure <| .deflate <| .done (.doneLeft rfl hp)
      | some out₁ =>
        match (← it₂.step).inflate with
        | .yield it₂' out₂ hp =>
          pure <| .deflate <| .yield (Intermediate.zip it₁ none it₂') (out₁, out₂)
            (.yieldRight rfl hp)
        | .skip it₂' hp =>
          pure <| .deflate <| .skip (Intermediate.zip it₁ (some out₁) it₂')
            (.skipRight rfl hp)
        | .done hp =>
          pure <| .deflate <| .done (.doneRight rfl hp)) := by
  simp only [Intermediate.zip, step, Iterator.step]
  split
  · apply bind_congr
    intro step
    cases step.inflate using PlausibleIterStep.casesOn <;> rfl
  · rename_i heq
    cases heq
    apply bind_congr
    intro step
    cases step.inflate using PlausibleIterStep.casesOn <;> rfl

section Array

-- Test that `forInNew` forces all mut vars into the same universe
example {α} (mask : Array Bool) (xs : Array α) : Array α := Id.run do
  let mut ys := #[]
  for b in mask, x in xs do
    if b then ys := ys.push x
  return ys

example (xs : Array Nat) : Id (Array String) := do
  let mut res := #[]
  for x in xs do
    if res.size > 0 then
      match res.back!, x with
      | x, 0 => res := res.set! (res.size - 1) x
      | x, n => res := res.set! (res.size - 1) (x ++ toString n)
    else res := res.push (toString x)
  return res

end Array

namespace Repros

-- Extracted from Lake.Build.Run. Tests if postponement and coercion insertion.
example : StateM (Nat × String) Unit := do
  let resetCtrl ← modifyGet fun s => (s.fst, {s with snd := ""})
  if resetCtrl.isValidChar then
    pure ()

structure AppImplicitArg where s : Term
def AppImplicitArg.syntax? (arg : AppImplicitArg) : Option Syntax := some arg.s

-- Extracted from Lean.PrettyPrinter.Delab.Builtins. Tests the interaction between `match` elaboration
-- and default instances.
example (fnStx : Syntax) (args : Array AppImplicitArg) : Option Syntax := do
  let x ← pure (f := Option) none <|> pure (f := Option) none
  match x with
  | none => have args : Array Syntax := args.filterMap (·.syntax?); return fnStx
  | some stx => return stx

-- Extracted from Lean.Language.Util. Tests that we try elaborating the join point RHS when
-- elaboration of the match fails
open Lean Language SnapshotTask in
partial example (s : SnapshotTree) : CoreM Unit :=
  go .skip s
where go range? s := do
  match range? with
  | .some _ => pure ()
  | .inherit => pure ()
  | .skip => pure ()
  s.children.toList.forM fun c => go c.reportingRange c.get

-- Extracted from Lean.Compiler.LCNF.Specialize.lean. Tests that we default when elaborating the
-- return argument.
example (paramsInfo : Array Nat) (args : Array Nat) : Array Nat := Id.run do
  let mut result := #[]
  for info in paramsInfo, arg in args do
    result := result.push arg
  pure <| result ++ args[paramsInfo.size...*]

-- Extracted from Lake.Config.Artifact. Tests that we allow pending instance resolution problems in
-- match discriminants which can be resolved when elaborating the match RHS.
example (data : Json) (k : String → Except String α) : Except String α := do
  match fromJson? data with
  | .ok out => k out
  | .error e => throw s!"artifact in unexpected JSON format: {e}"

-- Reproducer from Paul for testing that we elaborate the ρ synthesizing default instances.
example : Id Unit := do
  for x in 1...5 do
    pure ()
  return

structure MatchAltView' where
  patterns : Array Nat

open Lean Meta in
example (alt : MatchAltView') (collect : Nat → MetaM Nat) : MetaM (MatchAltView') := do
  let patterns ← alt.patterns.mapM fun p => do
    trace[Elab.match] "{p}"
    collect p
  return { alt with patterns := patterns }

set_option trace.Elab.do true in
set_option trace.Elab.match true in
example (tf : Float) (qf? : Option Float) : Id Unit := do
  if match qf? with | none => true | some qf => tf < qf then
    pure ()

set_option backward.do.legacy true in
set_option trace.Elab.match true in
example (tf : Float) (qf? : Option Float) : Id Unit := do
  if match qf? with | none => true | some qf => tf < qf then
    pure ()

-- This test ensures that `doLetElse` does not interpret the structure as a `doSeqBracketed`.
example (x : Nat) : Id (Bool × Bool) := do
  let 42 := x | { fst := true, snd := false } |> pure
  { fst := true, snd := false } |> pure

-- Test that `_ ← e` is allowed to discard results. (Implication: Can't expand to `x ← e`).
example (x : Nat) : Id Nat := do
  _ ← pure true
  return 0

-- This test documents a regression wrt. the old do elaborator. Note that the result type of the
-- match (i.e., the type of `mvar'`) will be a metavariable `?m.7` (which *might* depend on `e`).
-- Since `?m.7` occurs in the type of `jp : MVarId → MetaM ?m.7` and `?m.7` is weakly dependent on
-- `e`, we generalize the match to include `jp` as a discriminant. But the type of `jp` contains a
-- metavariable which leads to indefinite postponement before calling the match compiler.
-- The old elaborator did not generalize over `jp` because it was let-bound, not have-bound.
-- The workaround is to turn off generalization (`(generalizing := false)`) or to provide an
-- expected type for `mvar'`.
/--
error: Invalid field notation: Type of
  mvar'
is not known; cannot resolve field `withContext`

Hint: Consider replacing the field projection with a call to one of the following:
  • `MVarId.withContext`
  • `MessageData.withContext`
  • `Grind.Goal.withContext`
-/
#guard_msgs(error) in
open Lean Meta in
example (subgoals : List (Option Expr × MVarId)) : MetaM Unit :=
  discard <| subgoals.mapM fun ⟨e, mv⟩ ↦ do
    let mvar' ← match e with | none => pure mv | some _ => pure mv
    mvar'.withContext <| mvar'.assign Nat.mkType

open Lean Meta in
example (subgoals : List (Option Expr × MVarId)) : MetaM Unit :=
  discard <| subgoals.mapM fun ⟨e, mv⟩ ↦ do
    let mvar' : MVarId ← match e with | none => pure mv | some _ => pure mv
    mvar'.withContext <| mvar'.assign Nat.mkType

example (subgoals : List (Option Expr × MVarId)) : MetaM Unit :=
  discard <| subgoals.mapM fun ⟨e, mv⟩ ↦ do
    let mvar' ← match (generalizing := false) e with | none => pure mv | some _ => pure mv
    mvar'.withContext <| mvar'.assign Nat.mkType

end Repros

-- test case doLetElse
example (x : Nat) : IO (Fin (x + 1)) := do
  let 2 := x | return 0
  -- the pattern match performed a substitution
  let y : Fin 3 := ⟨1, by decide⟩
  return y

-- Test: Try/catch with let mut and match refinement
#check Id.run <| ExceptT.run (ε:=String) (α := Fin 17) doo
  let mut x := 0
  try
    if true then
      x := 10
      match h : x with
      | 2 => return ⟨x, by grind⟩
      | _ => return 0
    else
      x := 5
  catch e =>
    x := x + 1
  return ⟨3, by decide⟩

-- An example of a dependent match that does not refine the result type, but still refines one of
-- the free variables
set_option trace.Elab.match true in
example (x : Nat) : Nat :=
  have y : Fin (x + 1) := ⟨x, by grind⟩
  match x with
  | 42 => y
  | _ => 0

-- set_option backward.do.legacy true in
/-- info: "ok" -/
#guard_msgs in
#eval Id.run do
  let mut x := 0
  let y <- do
    let true := false | do x := x + 3; pure 0
    x := x + 100
    return "unreachable"
  if x + y < 23 then pure "ok" else pure "wrong"

set_option pp.raw false in
-- Full-blown dependent match including refinement of the join point and mut vars:
example (x : Nat) := Id.run (α := Fin (2 * x + 2)) do
  -- have y' : Fin (x + 1) := ⟨0, by grind⟩
  let mut y₁ : Fin (x + 1) := ⟨0, by grind⟩
  let y₂ : Fin (x + 1) ←
    match h : x with
    | z + 1 => y₁ := ⟨1, by grind⟩; pure ⟨1, by grind⟩
    | _     => pure ⟨0, by grind⟩
  return ⟨y₁.val + y₂.val, by grind⟩

-- Providing a motive... is not currently supported
/--
error: The `do` elaborator does not support custom motives. Try type ascription to provide expected types.
-/
#guard_msgs (error) in
example (x : Nat) := Id.run (α := Fin (2 * x + 2)) do
  have y' : Fin (x + 1) := ⟨0, by grind⟩
  let mut y₁ : Fin (x + 1) := ⟨0, by grind⟩
  let y₂ ←
    match (motive := ∀ x, Fin (x + 1)) x with
    | z + 1 => pure ⟨1, by grind⟩
    | _     => pure ⟨0, by grind⟩
  return ⟨y₁.val + y₂.val, by grind⟩

-- The motive is the result type of the join point and it is not refined without generalization.
-- If we dependently match on `x`, the first RHS has type `Fin (x + 2)` but is expected to have type
-- `Fin (0 + 2)`.
-- set_option backward.do.legacy true in
set_option trace.Elab.do true in
set_option trace.Elab.do.match true in
def depMatchNeedsGeneralization (x : Nat) := Id.run (α := Fin (x + 2)) do
  let y : Fin (x + 1) <-
    match (generalizing := false) x with
    | 0 => pure ⟨0, sorry⟩
    | _ => pure ⟨0, sorry⟩
  return ⟨y + 1, sorry⟩

example (x : Nat) (h : x = 3) := Id.run (α := Fin (x + 2)) do
  let y : Fin (x + 1) <-
    match hh : h with
    | rfl => pure ⟨0, by grind⟩
  return ⟨y + 1, by grind⟩

example (x : Nat) (h : x = 3) := Id.run (α := Fin (x + 2)) do
  let y : Fin (x + 1) <-
    match (generalizing := false) h with
    | rfl => pure ⟨0, by grind⟩
  return ⟨y + 1, by grind⟩

-- It would be too tedious to fix the following example.
-- We would need to kabstract the new discriminant `z + z` in any of the join point types in order
-- to determine whether we need to generalize. It's like collecting forward dependencies but with
-- arbitrary patterns. We don't support this; the user should instead specify `x` as a discriminant.
/--
error: The inferred match motive ⏎
  Fin (x + x)
or the monadic result type ⏎
  Id (Fin (x + x))
had occurrences of free variables that depend on the discriminants, but no continuation variables were generalized.
This is not supported by the `do` elaborator. Supply missing indices as disciminants to fix this.
-/
#guard_msgs (error) in
example (x z : Nat) (h : x = z + z) := Id.run (α := Fin (x + (z + z))) do
  let y : Fin (x + z + z) <- match h with | rfl => pure ⟨0, by grind⟩
  return ⟨y - 1, by grind⟩

-- Full-blown dependent match + try/catch + early return
example (p n : Nat) := Id.run <| ExceptT.run (α := Fin (2 * p + 2)) (ε:=String) do
let mut a := 0    have y' : Fin (p + 1) := ⟨0, by grind⟩
  let mut y₁ : Fin (p + 1) := ⟨0, by grind⟩
  let y₂ : Fin (p + 1) ←
    match h : p with
    | z + 1 => y₁ := ⟨1, by omega⟩; return ⟨3, by omega⟩
    | _     => pure ⟨0, by omega⟩
  return ⟨y₁.val + y₂.val, by grind⟩

-- Full-blown dependent match + try/catch, early return and break/continue
set_option trace.Elab.do.match true in
example (p n : Nat) : Except String (Fin (2 * p + 2)) := Id.run <| ExceptT.run do
  let mut a := 0
  for i in [n:n+10].toList do
    try
      have y' : Fin (p + 1) := ⟨0, by grind⟩
      let mut y₁ : Fin (p + 1) := ⟨0, by grind⟩
      let y₂ : Fin (p + 1) ←
        match h : p with
        | z + 1 => y₁ := ⟨1, by grind⟩; return ⟨3, by grind⟩
        | _     => pure ⟨0, by grind⟩
      if i = 5 then return ⟨y₁.val + y₂.val, by grind⟩
      if i = 15 then break
      if i = 25 then continue
      if i = 35 then throw "error"
      a := a + i
    catch _ =>
      a := a + 1
  return 0

-- Example for why `match` needs to generalize join points
-- set_option backward.do.legacy true in
example (x : Nat) : Id (Fin (x + 2)) := do
  let mut a := 1
  let mut b := 2
  let mut c := 3
  let r : Fin (x + 1) ←
    if a = 1 then
      match x with
      | 0 => a := a + 1; pure 0
      | _ => pure 0
    else
      b := b + 1; pure 0
  if a + b + c < 10 then
    pure 0
  else
    pure ⟨r + 1, sorry⟩

example (x : Nat) : Id (Fin (x + 2)) :=
  have a := 1
  have b := 2
  have c := 3
  have jp (r : Fin (x + 1)) a b c : Id (Fin (x + 2)) :=
    if a + b + c < 10 then
      pure 0
    else
      pure ⟨r + 1, sorry⟩
  if a = 1 then
    match (motive := ∀ x (jp : Fin (x + 1) → (a b c : Nat) → Id (Fin (x + 2))), Id (Fin (x + 2))) x, jp with
    | 0, jp => let a := a + 1; jp 0 a b c
    | _, jp => jp 0 a b c
  else
    have b := b + 1; jp 0 a b c

set_option trace.Compiler true in
example (x : Nat) : Id (Fin (x + 2)) :=
  have a := 1
  have b := 2
  have c := 3
  have jp (r : Fin (x + 1)) a b : Id (Fin (x + 2)) :=
    if a + b + c < 10 then
      pure 0
    else
      pure ⟨r + 1, sorry⟩
  if a = 1 then
    match (motive := ∀ x (jp : Fin (x + 1) → (a b : Nat) → Id (Fin (x + 2))), Id (Fin (x + 2))) x, jp with
    | 0, jp => let a := a + 1; jp 0 a b
    | _, jp => jp 0 a b
  else
    have b := b + 1; jp 0 a b

set_option backward.do.legacy false in
#eval Id.run <| ExceptT.run (ε:=String) do
  let res ←
    let false := true | pure true
    return 44
  if res then pure 23 else return 33

-- Test: Try/catch with let mut and match refinement
#eval Id.run <| ExceptT.run (ε:=String) (α := Fin 17) do
  let mut x : Fin 11 := 0
  let res ← try
    if true then
      x := 10
      pure (0 : Fin 1)
      -- let 2 := x | pure (0 : Fin 1)
      -- return ⟨x, by decide⟩
    else
      x := 5
      pure (0 : Fin 1)
  catch e =>
    x := x + 1
    pure (0 : Fin 1)
  let y := ↑res + ↑x + 3
  return ⟨y, by grind⟩

-- The following example was lifted from test case optionGetD prior to fixing
-- the `doFor` expander to emit a non-generalizing `match`.
-- Both the outer `match` and the inner `if` introduce JPs.
-- But since the outer `jpo` is duplicable, the inner `jpi` will turn out to be dead.
-- It is difficult to synthesize a `joinRhs` for `jpi` in this case, in particular because
-- the context might have changed since the introduction of `jpo`.
-- But we need to synthesize a `joinRhs` to substitute for `jpi`.
-- So there is some special code for the 0 jumps case that ensures
-- `joinRhs := fun _ (s : σ) => (s : mγ)` is well-typed.
example : IO Nat := do
  let mut i := 1
  for x in Loop.mk do
    match (generalizing := true) x with
    | _ =>
      if i < 10 then
        i := i + 1
      else
        break
  return i

set_option trace.Meta.Match.debug true in
set_option trace.Elab.do true in
example (a b : Nat) (h : a = b) : Nat := Id.run do
  match a, b, h with
  | _, _, rfl => return 0

-- Test that dependent matches do not leave behind unnecessary join point discriminants
set_option trace.Elab.do true in
example (o1 : Option Unit) (o2 : Option Unit) : Bool := Id.run do
  let b ←
    match o1 with
    | some _ => pure true
    | none =>
      match o2 with
      | some _ => pure true
      | none => pure false
  return b && b

-- extracted from grind_field_panic.lean
example (provided : Expr) : MetaM Expr := do
  let some className ← isClass? provided | failure
  let args : Array Expr := #[]
  let args ← args.mapM fun arg => do
      arg.fvarId!.getUserName
  return provided

/--
error: Application type mismatch: The argument
  h1
has type
  ¬iter1✝.IsAtEnd
but is expected to have type
  iter1 ≠ str1.endPos
in the application
  iter1.next h1
-/
#guard_msgs(error) in
example (str1 str2 : String) : Unit := Id.run do
  let mut iter1 := str1.startPos
  while h1 : ¬iter1.IsAtEnd do
    let mut iter2 := str2.startPos
    while h2 : ¬iter2.IsAtEnd do
      iter2 := iter2.next h2
      iter1 := iter1.next h1

example (str1 str2 : String) : Unit := Id.run do
  let mut iter1 := str1.startPos
  while h1 : ¬iter1.IsAtEnd do
    let mut iter2 := str2.startPos
    while h2 : ¬iter2.IsAtEnd do
      let cur := iter1.get h1
      iter2 := iter2.next h2
    iter1 := iter1.next h1

set_option trace.Elab.do true in
-- set_option trace.Meta.isDefEq true in
-- set_option trace.Meta.isDefEq.stuck true in
-- set_option trace.Meta.isDefEq.assign true in
/-
The following example used to trigger a bug in `LocalContext.findFromUserNames` where the index
of the current declaration was tracked redundantly and incorrectly.
-/
def getZoneRules (id : String) : Except IO.Error Nat := do
  let mut start : Int := -2147483648
  let mut initialLocalTimeType : Nat := 0
  while true do
    let result : Option (Int × Int) ← pure (some (1, (2:Int)))
    if let some res := result then
      if res.fst ≤ start ∨ res.fst >= 32503690800 then
        break
      start := 0
    else
      break
  return initialLocalTimeType

example (toolchainFile : System.FilePath) : IO (Option Int) := do
  try
    let toolchainString ← IO.FS.readFile toolchainFile
    return some <| 42
  catch
    | .noFileOrDirectory .. =>
      return none
    | e => throw e

example (url : String) (headers : Array String := #[]) (thing : Except String Lake.JsonObject): IO Nat := do
  match thing with
  | .ok data =>
    match (data.get? "response_code" <|> data.get? "http_code") with
    | .ok (some code) => return code
    | _ => panic s!"curl's JSON output did not contain a response code"
  | .error e =>
    panic s!"curl produced invalid JSON output: {e}"

open Lean.Server in
example (handler : LspResponse respType → RequestM α)
    (r : SerializedLspResponse) (response : Json) [FromJson respType] : RequestM α := do
  let .ok response := fromJson? response
    | throw <| RequestError.internalError "Failed to convert response of previous request handler when chaining stateful LSP request handlers"
  let r := { r with response := response }
  handler r

example (url : String) (headers : Array String := #[]) (thing : Except String Lake.JsonObject): IO Nat :=
  match thing with
  | .ok data =>
    match (data.get? "response_code" <|> data.get? "http_code") with
    | .ok (some code) => return code
    | _ => panic s!"curl's JSON output did not contain a response code"
  | .error e =>
    panic s!"curl produced invalid JSON output: {e}"

-- set_option trace.Elab.match true in
-- set_option trace.Elab.step true in
-- set_option trace.Elab.do true in
-- set_option trace.Elab.do.step true in
-- set_option trace.Elab.postpone true in
-- set_option backward.do.legacy true in
example (cache : Std.HashMap (Nat × Nat) Bool) : Bool := Id.run do
  let key := ⟨1, 2⟩
  match cache[key]? with
  | some r => return true
  | none => pure ()
  let := cache.contains key
  return false

end Blah

example : MetaM Bool := do
  let cfg := (← read).config
  return cfg.beta

example [Monad m] : ForIn' m (Option α) α inferInstance where
  forIn' x init f := do
    match x with
    | none => return init
    | some a =>
      match ← f a rfl init with
      | .done r | .yield r => return r

elab_rules : doElem <= dec
  | `(doElem| for $x:ident in $xs invariant $cursorBinder $stateBinders* => $body do $doSeq) => do
    --trace[Elab.do] "cursorBinder: {cursorBinder}"
    let call ← elabDoElem (← `(doElem| for $x:ident in $xs do $doSeq)) dec (catchExPostpone := false)
    mapLetTelescope call fun _xs call => do -- ForIn may introduce a break join point
    let_expr bind@Bind.bind m instBind σ γ call k := call
      | throwError "Internal elaboration error: `for` loop did not elaborate to a call of `Bind.bind`; got {call}."
    let_expr ForIn.forIn m ρ α instForIn σ xs s f := call
      | throwError "Internal elaboration error: `for` loop bind argument did not elaborate to a call of `ForIn.forIn`; got {call}."
    call.withApp fun head args => do
    let [u, v, w, x] := head.constLevels!
      | throwError "`Foldable.foldrEta` had wrong number of levels {head.constLevels!}"
    let mi := (← read).monadInfo
    unless ← isLevelDefEq mi.u (mkLevelMax v w) do
      throwError "The universe level of the monadic result type {mi.u} was not the maximum of that of the state tuple {w} and elements {v}. Cannot elaborate invariants for this case."
    unless ← isLevelDefEq mi.v x do
      throwError "The universe level of the result type {mi.v} and that of the continuation result type {x} were different. Cannot elaborate invariants for this case."
    -- First the non-ghost arguments
    let instMonad ← Term.mkInstMVar (mkApp (mkConst ``Monad [mi.u, mi.v]) mi.m)
    let app := mkConst ``ForIn.forInInv [u, v, w, x]
    let app := mkApp5 app m ρ α instForIn σ
    let app := mkApp3 app xs s f
    -- Now the ghost arguments
    let instForIn ← Term.mkInstMVar (mkApp3 (mkConst ``ForIn [u, v, v, v]) (mkConst ``Id [v]) ρ α)
    let ps ← mkFreshExprMVar (mkConst ``Std.Do.PostShape [mi.u])
    let instWP ← Term.mkInstMVar (mkApp2 (mkConst ``Std.Do.WP [mi.u, mi.v]) (← read).monadInfo.m ps)
    let xsToList := mkApp4 (mkConst ``ForIn.toList [u, v]) ρ α instForIn xs
    let cursor := mkApp2 (mkConst ``List.Cursor [v]) α xsToList
    let assertion := mkApp (mkConst ``Std.Do.Assertion [mi.u]) ps
    let mutVarsTuple ← Term.exprToSyntax s
    let cursorσ := mkApp2 (mkConst ``Prod [v, mi.u]) cursor σ
    let success ← Term.elabFun (← `(fun ($cursorBinder, $mutVarsTuple) $stateBinders* => $body)) (← mkArrow cursorσ assertion)
    let inv := mkApp3 (mkConst ``Std.Do.PostCond.noThrow [mkLevelMax v mi.u]) ps cursorσ success
    let forIn := mkApp5 app instMonad instForIn ps instWP inv
    return mkApp6 bind m instBind σ γ forIn k

set_option trace.Elab.do true in
example (elems : Syntax.TSepArray `term ",") : MacroM Syntax := doo
  -- NOTE: we do not have `TSepArray.getElems` yet at this point
  let rec expandListLit (i : Nat) (skip : Bool) (result : TSyntax `term) : MacroM Syntax := doo
    match i, skip with
    | 0,   _     => pure result
    | i+1, true  => expandListLit i false result
    | i+1, false => expandListLit i true  (← ``(List.cons $(⟨elems.elemsAndSeps.get!Internal i⟩) $result))
  let size := elems.elemsAndSeps.size
  if size < 64 then
    expandListLit size (size % 2 == 0) (← ``(List.nil))
  else
    `(%[ $elems,* | List.nil ])

#check doo return 42
set_option trace.Elab.do true in
-- set_option trace.Meta.isDefEq true in
set_option trace.Meta.isDefEq.assign true in
#check Id.run (α := Nat) doo
  let mut x := 42
  return x
set_option trace.Elab.do true in
set_option pp.raw false in
#check Id.run (α := Nat) doo
  let mut x ← pure 42
  let y ←
    if true then
      pure 42
    else
      pure 31
  x := x + y
  return x
set_option pp.mvars.delayed false in
set_option trace.Meta.synthInstance true in
set_option trace.Elab.step false in
set_option trace.Elab.do true in
set_option trace.Elab.postpone true in
set_option pp.raw false in
#check doo return 42
#check doo pure (); return 42
#check doo let mut x : Nat := 0; if true then {x := x + 1} else {pure ()}; pure x
#check doo let mut x : Nat := 0; if true then {pure ()} else {pure ()}; pure 13
#check doo let x : Nat := 0; if true then {pure ()} else {pure ()}; pure 13
set_option trace.Elab.do true in
#check Id.run <| ExceptT.run doo
  let e ← try
      let x := 0
      let _ := 42
      throw "error"
    catch e : String =>
      pure e
  return e

set_option trace.Meta.isDefEq true in
#check fun e => Id.run doo
  let mut x := 0
  let y := 3
  let z ← do
    let mut y ← e
    x := y + 1
    pure y
  let y := y + 3
  pure (x + y + z)

set_option trace.Compiler.saveBase true in
set_option trace.Compiler.specialize.step true in
set_option trace.Elab.do true in
#eval Id.run doo
  let mut x := 42
  for i in [1,2,3] do
    for j in [i:10].toList do
      x := x + i + j
  return x

set_option trace.Elab.do true in
/--
trace: [Elab.do] have x := 1;
    do
    let __s ←
      forIn [1, 2, 3] x fun i __s =>
          let x_1 := __s;
          do
          let __s_1 ←
            forIn [4, 5, 6] x_1 fun j __s_1 =>
                let x_2 := __s_1;
                have __do_jp := fun __r x_3 =>
                  have __do_jp := fun __r_1 x_4 =>
                    if j > 6 then pure (ForInStep.done x_4) else pure (ForInStep.yield x_4);
                  if j < 3 then pure (ForInStep.yield x_3) else __do_jp PUnit.unit x_3;
                if j < 5 then
                  have x := x_2 + j;
                  __do_jp PUnit.unit x
                else __do_jp PUnit.unit x_2
          let x_2 : ?m.177 := __s_1
          if x_2 > 20 then pure (ForInStep.done x_2) else pure (ForInStep.yield x_2)
    let x : ?m.177 := __s
    pure x
-/
#guard_msgs in
example := Id.run doo
  let mut x := 1
  for i in [1,2,3] do
    for j in [4,5,6] do
      if j < 5 then x := x + j
      if j < 3 then continue
      if j > 6 then break
    if x > 20 then break
  return x

set_option trace.Compiler.saveBase true in
set_option trace.Elab.do true in
#eval Id.run doo
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] do
    x := x + i
    for j in [i:10].toList do
      if j < 5 then z := z + j
      z := z + i
  return x + y + z

/--
info: (have x := 42;
  have y := 0;
  have z := 1;
  do
  let __s ←
    forIn [1, 2, 3] (x, z) fun i __s =>
        let x := __s.fst;
        let z := __s.snd;
        have x := x + i;
        have __do_jp := fun __r x y z =>
          have z := z + i;
          pure (ForInStep.yield (x, z));
        if x > 10 then
          have z := z + i;
          __do_jp PUnit.unit x y z
        else __do_jp PUnit.unit x y z
  let x : Nat := __s.fst
  let z : Nat := __s.snd
  pure (x + y + z)).run : Nat
-/
#guard_msgs (info) in
#check (Id.run doo
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] do
    x := x + i
    if x > 10 then z := z + i
    z := z + i
  return x + y + z)

-- set_option trace.Meta.isDefEq true in
-- set_option trace.Meta.isDefEq.delta true in
-- set_option trace.Meta.isDefEq.assign true in
-- set_option trace.Elab.do true in
/--
info: (have w := 23;
  have x := 42;
  have y := 0;
  have z := 1;
  do
  let __s ←
    forIn [1, 2, 3] (x, y, z) fun i __s =>
        let x := __s.fst;
        let __s_1 := __s.snd;
        let y := __s_1.fst;
        let z := __s_1.snd;
        have __do_jp := fun __r w x y z =>
          have __do_jp := fun __r w x y z =>
            have __do_jp := fun __r w x y z =>
              have x := x + i;
              pure (ForInStep.yield (x, y, z));
            if x > 10 then
              have x := x + 3;
              pure (ForInStep.yield (x, y, z))
            else __do_jp PUnit.unit w x y z;
          if x = 3 then
            have z := z + i;
            __do_jp PUnit.unit w x y z
          else __do_jp PUnit.unit w x y z;
        if x < 20 then
          have y := y - 2;
          pure (ForInStep.done (x, y, z))
        else __do_jp PUnit.unit w x y z
  let x : Nat := __s.fst
  let __s : Nat × Nat := __s.snd
  let y : Nat := __s.fst
  let z : Nat := __s.snd
  pure (w + x + y + z)).run : Nat
-/
#guard_msgs (info) in
#check Id.run doo
  let mut w := 23
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] do
    if x < 20 then y := y - 2; break
    if x = 3 then z := z + i
    if x > 10 then x := x + 3; continue
    x := x + i
  return w + x + y + z

set_option trace.Compiler.saveBase true in
/--
trace: [Compiler.saveBase] size: 20
    def Do._example : Nat :=
      let w := 23;
      let x := 42;
      let y := 0;
      let z := 1;
      let _x.1 := 2;
      let _x.2 := 3;
      let _x.3 := @List.nil _;
      let _x.4 := @List.cons _ _x.2 _x.3;
      let _x.5 := @List.cons _ _x.1 _x.4;
      let _x.6 := @List.cons _ z _x.5;
      let _x.7 := @Prod.mk _ _ y z;
      let _x.8 := @Prod.mk _ _ x _x.7;
      let _x.9 := List.forIn'.loop._at_.Do._example.spec_0 _x.6 _x.6 _x.8 ◾;
      let _x.10 := _x.9 # 0;
      let _x.11 := _x.9 # 1;
      let _x.12 := _x.11 # 0;
      let _x.13 := _x.11 # 1;
      let _x.14 := Nat.add w _x.10;
      let _x.15 := Nat.add _x.14 _x.12;
      let _x.16 := Nat.add _x.15 _x.13;
      return _x.16
[Compiler.saveBase] size: 37
    def List.forIn'.loop._at_.Do._example.spec_0 as x.1 x.2 x.3 : Nat × Nat × Nat :=
      let _x.4 := 3;
      let _x.5 := 2;
      cases x.1 : Nat × Nat × Nat
      | List.nil =>
        return x.2
      | List.cons head.6 tail.7 =>
        jp _jp.8 x y z : Nat × Nat × Nat :=
          let _x.9 := 10;
          let _x.10 := Nat.decLt _x.9 x;
          cases _x.10 : Nat × Nat × Nat
          | Decidable.isFalse x.11 =>
            let _x.12 := Nat.add x head.6;
            let _x.13 := @Prod.mk _ _ y z;
            let _x.14 := @Prod.mk _ _ _x.12 _x.13;
            let _x.15 := List.forIn'.loop._at_.Do._example.spec_0 as tail.7 _x.14 ◾;
            return _x.15
          | Decidable.isTrue x.16 =>
            let _x.17 := Nat.add x _x.4;
            let _x.18 := @Prod.mk _ _ y z;
            let _x.19 := @Prod.mk _ _ _x.17 _x.18;
            let _x.20 := List.forIn'.loop._at_.Do._example.spec_0 as tail.7 _x.19 ◾;
            return _x.20;
        let _x.21 := x.2 # 0;
        let _x.22 := x.2 # 1;
        let _x.23 := _x.22 # 0;
        let _x.24 := _x.22 # 1;
        let _x.25 := 20;
        let _x.26 := Nat.decLt _x.21 _x.25;
        cases _x.26 : Nat × Nat × Nat
        | Decidable.isFalse x.27 =>
          let _x.28 := instDecidableEqNat _x.21 _x.4;
          cases _x.28 : Nat × Nat × Nat
          | Decidable.isFalse x.29 =>
            goto _jp.8 _x.21 _x.23 _x.24
          | Decidable.isTrue x.30 =>
            let _x.31 := Nat.add _x.24 head.6;
            goto _jp.8 _x.21 _x.23 _x.31
        | Decidable.isTrue x.32 =>
          let _x.33 := Nat.sub _x.23 _x.5;
          let _x.34 := @Prod.mk _ _ _x.33 _x.24;
          let _x.35 := @Prod.mk _ _ _x.21 _x.34;
          return _x.35
-/
#guard_msgs in
example := Id.run doo
  let mut w := 23
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] do
    if x < 20 then y := y - 2; break
    if x = 3 then z := z + i
    if x > 10 then x := x + 3; continue
    x := x + i
  return w + x + y + z

set_option trace.Elab.do true in
/--
trace: [Elab.do] have x := 42;
    have y := 0;
    do
    let __s ←
      forIn [1, 2, 3] x fun i __s =>
          let x_1 := __s;
          have __do_jp := fun __r x_2 y_1 =>
            have __do_jp := fun __r_1 x_3 y_2 =>
              have __do_jp := fun __r_2 x_4 y_3 =>
                have x := x_4 + i;
                pure (ForInStep.yield x);
              if x_3 < 20 then
                have x := x_3 - 2;
                pure (ForInStep.done x)
              else __do_jp PUnit.unit x_3 y_2;
            if x_2 > 10 then
              have x := x_2 + 3;
              pure (ForInStep.yield x)
            else __do_jp PUnit.unit x_2 y_1;
          if x_1 = 3 then
            have x := x_1 + 1;
            __do_jp PUnit.unit x y
          else __do_jp PUnit.unit x_1 y
    let x_1 : ?m.184 := __s
    pure (x_1 + x_1 + x_1 + x_1)
-/
#guard_msgs in
example := Id.run doo
  let mut x := 42
  let mut y := 0
  for i in [1,2,3] do
    if x = 3 then x := x + 1
    if x > 10 then x := x + 3; continue
    if x < 20 then x := x - 2; break
    x := x + i
  return x + x + x + x

/-
info: (let w := 23;
  let x := 42;
  let y := 0;
  let z := 1;
  do
  let r ←
    forIn [1, 2, 3] ⟨x, y, z⟩ fun i r =>
        let x := r.fst;
        let x_1 := r.snd;
        let y := x_1.fst;
        let z := x_1.snd;
        let __do_jp := fun x y z y_1 =>
          let __do_jp := fun x z y_2 =>
            let __do_jp := fun x y_3 =>
              let x := x + i;
              do
              pure PUnit.unit
              pure (ForInStep.yield ⟨x, y, z⟩);
            if x > 10 then
              let x := x + 3;
              pure (ForInStep.yield ⟨x, y, z⟩)
            else do
              let y ← pure PUnit.unit
              __do_jp x y;
          if x = 3 then
            let z := z + i;
            do
            let y ← pure PUnit.unit
            __do_jp x z y
          else do
            let y ← pure PUnit.unit
            __do_jp x z y;
        if x < 20 then
          let y := y - 2;
          pure (ForInStep.done ⟨x, y, z⟩)
        else do
          let y_1 ← pure PUnit.unit
          __do_jp x y z y_1
  match r with
    | ⟨x, y, z⟩ => pure (w + x + y + z)).run : Nat
-/
-- #guard_msgs (info) in
#check (Id.run do
  let mut w := 23
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] do
    if x < 20 then y := y - 2; break
    if x = 3 then z := z + i
    if x > 10 then x := x + 3; continue
    x := x + i
  return w + x + y + z)

set_option trace.Elab.do true in
set_option trace.Compiler.saveBase true in
/--
trace: [Elab.do] have x := 42;
    do
    let __s ←
      forIn [1, 2, 3] (none, x) fun i __s =>
          let x_1 := __s.snd;
          have __do_jp := fun __r x_2 =>
            have __do_jp := fun __r_1 x_3 =>
              have __do_jp := fun __r_2 x_4 =>
                have x := x_4 + i;
                pure (ForInStep.yield (none, x));
              if x_3 < 20 then
                have x := x_3 * 2;
                pure (ForInStep.done (none, x))
              else __do_jp PUnit.unit x_3;
            if x_2 > 10 then
              have x := x_2 + 3;
              pure (ForInStep.yield (none, x))
            else __do_jp PUnit.unit x_2;
          if x_1 = 3 then pure (ForInStep.done (some x_1, x_1)) else __do_jp PUnit.unit x_1
    let __r : Option ?m.182 := __s.fst
    let x_1 : ?m.182 := __s.snd
    match __r with
      | some r => pure r
      | none =>
        have x_2 := x_1 + 13;
        have x_3 := x_2 + 13;
        have x_4 := x_3 + 13;
        have x := x_4 + 13;
        pure x
---
trace: [Compiler.saveBase] size: 21
    def Do._example : Nat :=
      let x := 42;
      let _x.1 := 1;
      let _x.2 := 2;
      let _x.3 := 3;
      let _x.4 := @List.nil _;
      let _x.5 := @List.cons _ _x.3 _x.4;
      let _x.6 := @List.cons _ _x.2 _x.5;
      let _x.7 := @List.cons _ _x.1 _x.6;
      let _x.8 := @none _;
      let _x.9 := @Prod.mk _ _ _x.8 x;
      let _x.10 := List.forIn'.loop._at_.Do._example.spec_0 _x.7 _x.7 _x.9 ◾;
      let _x.11 := _x.10 # 0;
      cases _x.11 : Nat
      | Option.none =>
        let _x.12 := _x.10 # 1;
        let _x.13 := 13;
        let _x.14 := Nat.add _x.12 _x.13;
        let _x.15 := Nat.add _x.14 _x.13;
        let _x.16 := Nat.add _x.15 _x.13;
        let _x.17 := Nat.add _x.16 _x.13;
        return _x.17
      | Option.some val.18 =>
        return val.18
[Compiler.saveBase] size: 31
    def List.forIn'.loop._at_.Do._example.spec_0 as x.1 x.2 x.3 : Option Nat × Nat :=
      let _x.4 := 3;
      let _x.5 := @none _;
      let _x.6 := 2;
      cases x.1 : Option Nat × Nat
      | List.nil =>
        return x.2
      | List.cons head.7 tail.8 =>
        let _x.9 := x.2 # 1;
        let _x.10 := instDecidableEqNat _x.9 _x.4;
        cases _x.10 : Option Nat × Nat
        | Decidable.isFalse x.11 =>
          let _x.12 := 10;
          let _x.13 := Nat.decLt _x.12 _x.9;
          cases _x.13 : Option Nat × Nat
          | Decidable.isFalse x.14 =>
            let _x.15 := 20;
            let _x.16 := Nat.decLt _x.9 _x.15;
            cases _x.16 : Option Nat × Nat
            | Decidable.isFalse x.17 =>
              let _x.18 := Nat.add _x.9 head.7;
              let _x.19 := @Prod.mk _ _ _x.5 _x.18;
              let _x.20 := List.forIn'.loop._at_.Do._example.spec_0 as tail.8 _x.19 ◾;
              return _x.20
            | Decidable.isTrue x.21 =>
              let _x.22 := Nat.mul _x.9 _x.6;
              let _x.23 := @Prod.mk _ _ _x.5 _x.22;
              return _x.23
          | Decidable.isTrue x.24 =>
            let _x.25 := Nat.add _x.9 _x.4;
            let _x.26 := @Prod.mk _ _ _x.5 _x.25;
            let _x.27 := List.forIn'.loop._at_.Do._example.spec_0 as tail.8 _x.26 ◾;
            return _x.27
        | Decidable.isTrue x.28 =>
          let _x.29 := @some _ _x.9;
          let _x.30 := @Prod.mk _ _ _x.29 _x.9;
          return _x.30
-/
#guard_msgs in
example := Id.run doo
  let mut x := 42
  for i in [1,2,3] do
    if x = 3 then return x
    if x > 10 then x := x + 3; continue
    if x < 20 then x := x * 2; break
    x := x + i
  x := x + 13
  x := x + 13
  x := x + 13
  x := x + 13
  return x

set_option trace.Compiler.saveBase true in
/--
trace: [Compiler.saveBase] size: 21
    def Do._example : Nat :=
      let x := 42;
      let _x.1 := 1;
      let _x.2 := 2;
      let _x.3 := 3;
      let _x.4 := @List.nil _;
      let _x.5 := @List.cons _ _x.3 _x.4;
      let _x.6 := @List.cons _ _x.2 _x.5;
      let _x.7 := @List.cons _ _x.1 _x.6;
      let _x.8 := @none _;
      let _x.9 := @Prod.mk _ _ _x.8 x;
      let _x.10 := List.forIn'.loop._at_.Do._example.spec_0 _x.7 _x.7 _x.9 ◾;
      let _x.11 := _x.10 # 0;
      cases _x.11 : Nat
      | Option.none =>
        let _x.12 := _x.10 # 1;
        let _x.13 := 13;
        let _x.14 := Nat.add _x.12 _x.13;
        let _x.15 := Nat.add _x.14 _x.13;
        let _x.16 := Nat.add _x.15 _x.13;
        let _x.17 := Nat.add _x.16 _x.13;
        return _x.17
      | Option.some val.18 =>
        return val.18
[Compiler.saveBase] size: 31
    def List.forIn'.loop._at_.Do._example.spec_0 as x.1 x.2 x.3 : Option Nat × Nat :=
      let _x.4 := 3;
      let _x.5 := @none _;
      let _x.6 := 2;
      cases x.1 : Option Nat × Nat
      | List.nil =>
        return x.2
      | List.cons head.7 tail.8 =>
        let _x.9 := x.2 # 1;
        let _x.10 := instDecidableEqNat _x.9 _x.4;
        cases _x.10 : Option Nat × Nat
        | Decidable.isFalse x.11 =>
          let _x.12 := 10;
          let _x.13 := Nat.decLt _x.12 _x.9;
          cases _x.13 : Option Nat × Nat
          | Decidable.isFalse x.14 =>
            let _x.15 := 20;
            let _x.16 := Nat.decLt _x.9 _x.15;
            cases _x.16 : Option Nat × Nat
            | Decidable.isFalse x.17 =>
              let _x.18 := Nat.add _x.9 head.7;
              let _x.19 := @Prod.mk _ _ _x.5 _x.18;
              let _x.20 := List.forIn'.loop._at_.Do._example.spec_0 as tail.8 _x.19 ◾;
              return _x.20
            | Decidable.isTrue x.21 =>
              let _x.22 := Nat.mul _x.9 _x.6;
              let _x.23 := @Prod.mk _ _ _x.5 _x.22;
              return _x.23
          | Decidable.isTrue x.24 =>
            let _x.25 := Nat.add _x.9 _x.4;
            let _x.26 := @Prod.mk _ _ _x.5 _x.25;
            let _x.27 := List.forIn'.loop._at_.Do._example.spec_0 as tail.8 _x.26 ◾;
            return _x.27
        | Decidable.isTrue x.28 =>
          let _x.29 := @some _ _x.9;
          let _x.30 := @Prod.mk _ _ _x.29 _x.9;
          return _x.30
-/
#guard_msgs in
example := Id.run doo
  let mut x := 42
  for i in [1,2,3] do
    if x = 3 then return x
    if x > 10 then x := x + 3; continue
    if x < 20 then x := x * 2; break
    x := x + i
  x := x + 13
  x := x + 13
  x := x + 13
  x := x + 13
  return x

set_option trace.Elab.do true in
set_option trace.Compiler.saveBase true in
/--
trace: [Elab.do] have x := 42;
    have y := 0;
    have z := 1;
    do
    let __s ←
      forIn [1, 2, 3] (x, z) fun i __s =>
          let x := __s.fst;
          let z := __s.snd;
          have x := x + i;
          do
          let __s ←
            forIn [i:10].toList z fun j __s =>
                let z := __s;
                have z := z + x + j;
                pure (ForInStep.yield z)
          let z : Nat := __s
          pure (ForInStep.yield (x, z))
    let x : Nat := __s.fst
    let z : Nat := __s.snd
    pure (x + y + z)
---
trace: [Compiler.saveBase] size: 13
    def Do._example : Nat :=
      let x := 42;
      let z := 1;
      let _x.1 := 2;
      let _x.2 := 3;
      let _x.3 := @List.nil _;
      let _x.4 := @List.cons _ _x.2 _x.3;
      let _x.5 := @List.cons _ _x.1 _x.4;
      let _x.6 := @List.cons _ z _x.5;
      let _x.7 := @Prod.mk _ _ x z;
      let _x.8 := List.forIn'.loop._at_.Do._example.spec_1 _x.6 _x.6 _x.7 ◾;
      let _x.9 := _x.8 # 0;
      let _x.10 := _x.8 # 1;
      let _x.11 := Nat.add _x.9 _x.10;
      return _x.11
[Compiler.saveBase] size: 6
    def List.forIn'.loop._at_.Do._example.spec_0 _x.1 as x.2 x.3 x.4 : Nat :=
      cases x.2 : Nat
      | List.nil =>
        return x.3
      | List.cons head.5 tail.6 =>
        let _x.7 := Nat.add x.3 _x.1;
        let _x.8 := Nat.add _x.7 head.5;
        let _x.9 := List.forIn'.loop._at_.Do._example.spec_0 _x.1 as tail.6 _x.8 ◾;
        return _x.9
[Compiler.saveBase] size: 17
    def List.forIn'.loop._at_.Do._example.spec_1 as x.1 x.2 x.3 : Nat × Nat :=
      let z := 1;
      cases x.1 : Nat × Nat
      | List.nil =>
        return x.2
      | List.cons head.4 tail.5 =>
        let _x.6 := x.2 # 0;
        let _x.7 := x.2 # 1;
        let _x.8 := Nat.add _x.6 head.4;
        let _x.9 := 10;
        let _x.10 := Nat.sub _x.9 head.4;
        let _x.11 := Nat.add _x.10 z;
        let _x.12 := Nat.sub _x.11 z;
        let _x.13 := Nat.add head.4 _x.12;
        let _x.14 := @List.nil _;
        let _x.15 := List.range'TR.go z _x.12 _x.13 _x.14;
        let _x.16 := List.forIn'.loop._at_.Do._example.spec_0 _x.8 _x.15 _x.15 _x.7 ◾;
        let _x.17 := @Prod.mk _ _ _x.8 _x.16;
        let _x.18 := List.forIn'.loop._at_.Do._example.spec_1 as tail.5 _x.17 ◾;
        return _x.18
-/
#guard_msgs in
example := Id.run doo
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] do
    x := x + i
    for j in [i:10].toList do
      z := z + x + j
  return x + y + z

/--
info: (have x := 42;
  do
  let __s ←
    forIn [1, 2, 3] (none, x) fun i __s =>
        let x := __s.snd;
        have __do_jp := fun __r x =>
          have __do_jp := fun __r x =>
            have __do_jp := fun __r x =>
              have x := x + i;
              pure (ForInStep.yield (none, x));
            if x < 20 then
              have x := x * 2;
              pure (ForInStep.done (none, x))
            else __do_jp PUnit.unit x;
          if x > 10 then
            have x := x + 3;
            pure (ForInStep.yield (none, x))
          else __do_jp PUnit.unit x;
        if x = 3 then pure (ForInStep.done (some x, x)) else __do_jp PUnit.unit x
  let __r : Option Nat := __s.fst
  let x : Nat := __s.snd
  match __r with
    | some r => pure r
    | none =>
      have x := x + 13;
      have x := x + 13;
      have x := x + 13;
      have x := x + 13;
      pure x).run : Nat
-/
#guard_msgs (info) in
#check (Id.run do
  let mut x := 42
  for i in [1,2,3] do
    if x = 3 then return x
    if x > 10 then x := x + 3; continue
    if x < 20 then x := x * 2; break
    x := x + i
  x := x + 13
  x := x + 13
  x := x + 13
  x := x + 13
  return x)

/--
info: (have x := 42;
  do
  let __s ←
    forIn [1, 2, 3] (none, x) fun i __s =>
        let x := __s.snd;
        have __do_jp := fun __r x =>
          have __do_jp := fun __r x =>
            have __do_jp := fun __r x =>
              have x := x + i;
              pure (ForInStep.yield (none, x));
            if x < 20 then
              have x := x * 2;
              pure (ForInStep.done (none, x))
            else __do_jp PUnit.unit x;
          if x > 10 then
            have x := x + 3;
            pure (ForInStep.yield (none, x))
          else __do_jp PUnit.unit x;
        if x = 3 then pure (ForInStep.done (some x, x)) else __do_jp PUnit.unit x
  let __r : Option Nat := __s.fst
  let x : Nat := __s.snd
  match __r with
    | some r => pure r
    | none =>
      have x := x + 13;
      have x := x + 13;
      have x := x + 13;
      have x := x + 13;
      pure x).run : Nat
-/
#guard_msgs (info) in
#check (Id.run do
  let mut x := 42
  for i in [1,2,3] do
    if x = 3 then return x
    if x > 10 then x := x + 3; continue
    if x < 20 then x := x * 2; break
    x := x + i
  x := x + 13
  x := x + 13
  x := x + 13
  x := x + 13
  return x)

open Std.Do in
set_option trace.Elab.do true in
#check Id.run doo
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3]
    invariant xs => ⌜xs.pos = 3⌝ do
    x := x + i
    for j in [i:10].toList do
      if j < 5 then z := z + j
      if j > 8 then return 42
      if j < 3 then continue
      if j > 6 then break
      z := z + i
  return x + y + z

open Std.Do in
#check Id.run <| StateT.run (σ:= Nat) (s:=42) doo
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3]
    invariant xs s => ⌜xs.pos = s⌝ do
    x := x + i
    for j in [i:10].toList do
      if j < 5 then z := z + j
      if j > 8 then return 42
      if j < 3 then continue
      if j > 6 then break
      z := z + i
  return x + y + z

#check Id.run do
  let mut a := 0
  for x in [1,2,3], y in [3,4,5] do
    a := a + x + y
  return a

example : (Id.run doo pure 42)
        = (Id.run  do pure 42) := by rfl
example : (Id.run doo return 42)
        = (Id.run  do return 42) := by rfl
example {e : Id PUnit} : (Id.run doo e)
                       = (Id.run  do e) := by rfl
example {e : Id PUnit} : (Id.run doo e; return 42)
                       = (Id.run  do e; return 42) := by rfl
example : (Id.run doo let x := 42; return x + 13)
        = (Id.run  do let x := 42; return x + 13) := by rfl
example : (Id.run doo let x ← pure 42; return x + 13)
        = (Id.run  do let x ← pure 42; return x + 13) := by rfl
example : (Id.run doo let mut x := 42; x := x + 1; return x + 13)
        = (Id.run  do let mut x := 42; x := x + 1; return x + 13) := by rfl
example : (Id.run doo let mut x ← pure 42; x := x + 1; return x + 13)
        = (Id.run  do let mut x ← pure 42; x := x + 1; return x + 13) := by rfl
example : (Id.run doo let mut x ← pure 42; if true then {x := x + 1; return x} else {x := x + 3}; x := x + 13; return x)
        = (Id.run  do let mut x ← pure 42; if true then {x := x + 1; return x} else {x := x + 3}; x := x + 13; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; let mut _x ← if true then {x := x + 1; let y ← pure 3; return y}; x := x + 13; return x)
        = (Id.run  do let mut x ← pure 42; let mut _x ← if true then {x := x + 1; let y ← pure 3; return y}; x := x + 13; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; x ← if true then {x := x + 1; return x} else {x := x + 2; pure 4}; return x)
        = (Id.run  do let mut x ← pure 42; x ← if true then {x := x + 1; return x} else {x := x + 2; pure 4}; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; let mut z := 0; let mut _x ← if true then {z := z + 1; let y ← pure 3; return y} else {z := z + 2; pure 4}; x := x + z; return x)
        = (Id.run  do let mut x ← pure 42; let mut z := 0; let mut _x ← if true then {z := z + 1; let y ← pure 3; return y} else {z := z + 2; pure 4}; x := x + z; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; let mut z := 0; z ← if true then {x := x + 1; return z} else {x := x + 2; pure 4}; x := x + z; return x)
        = (Id.run  do let mut x ← pure 42; let mut z := 0; z ← if true then {x := x + 1; return z} else {x := x + 2; pure 4}; x := x + z; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; let y ← if true then {pure 3} else {pure 4}; x := x + y; return x)
        = (Id.run  do let mut x ← pure 42; let y ← if true then {pure 3} else {pure 4}; x := x + y; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; let y ← if true then {pure 3} else {pure 4}; x := x + y; return x)
        = (Id.run  do let mut x ← pure 42; let y ← if true then {pure 3} else {pure 4}; x := x + y; return x) := by rfl
example : Nat := Id.run doo let mut foo : Nat = Nat := rfl; pure (foo ▸ 23)
example {e} : (Id.run doo let mut x := 0; let y := 3; let z ← do { let mut y ← e; x := y + 1; pure y }; let y := y + 3; pure (x + y + z))
            = (Id.run  do let mut x := 0; let y := 3; let z ← do { let mut y ← e; x := y + 1; pure y }; let y := y + 3; pure (x + y + z)) := by rfl
example : (Id.run doo let x := 0; let y ← let x := x + 1; pure x)
        = (Id.run doo let x := 0; pure x) := by rfl

-- Test: Nested if-then-else with multiple mutable variables
example : (Id.run doo
  let mut x := 0
  let mut y := 1
  if true then
    if false then
      x := 10
      y := 20
    else
      x := 5
      y := 15
  else
    x := 100
  return x + y)
= (Id.run do
  let mut x := 0
  let mut y := 1
  if true then
    if false then
      x := 10
      y := 20
    else
      x := 5
      y := 15
  else
    x := 100
  return x + y) := by rfl

-- Test: Multiple reassignments in sequence
example : (Id.run doo
  let mut x := 10
  x := x + 1
  x := x * 2
  x := x - 3
  return x)
= (Id.run do
  let mut x := 10
  x := x + 1
  x := x * 2
  x := x - 3
  return x) := by rfl

-- Test: Monadic bind with complex RHS
example : (Id.run doo
  let x ← (do let y := 5; pure (y + 3))
  return x * 2)
= (Id.run do
  let x ← (do let y := 5; pure (y + 3))
  return x * 2) := by rfl

-- Test: Mutable variable reassignment through monadic bind
example : (Id.run doo
  let mut x := 1
  x ← pure (x + 10)
  x ← pure (x * 2)
  return x)
= (Id.run do
  let mut x := 1
  x ← pure (x + 10)
  x ← pure (x * 2)
  return x) := by rfl

-- Test: Multiple mutable variables with different reassignment patterns
example : (Id.run doo
  let mut a := 1
  let mut b := 2
  let mut c := 3
  if true then
    a := a + 1
  else
    b := b + 1
  c := a + b
  return (a, b, c))
= (Id.run do
  let mut a := 1
  let mut b := 2
  let mut c := 3
  if true then
    a := a + 1
  else
    b := b + 1
  c := a + b
  return (a, b, c)) := by rfl

-- Test: Let binding followed by mutable reassignment
example : (Id.run doo
  let x := 5
  let mut y := x
  y := y * 2
  return (x, y))
= (Id.run do
  let x := 5
  let mut y := x
  y := y * 2
  return (x, y)) := by rfl

-- Test: Early return in else branch
example : (Id.run doo
  let mut x := 0
  if false then
    x := 10
  else
    return 42
  x := 20
  return x)
= (Id.run do
  let mut x := 0
  if false then
    x := 10
  else
    return 42
  x := 20
  return x) := by rfl

-- Test: Both branches return
example : (Id.run doo
  let mut x := 0
  if true then
    return 1
  else
    return 2)
= (Id.run do
  let mut x := 0
  if true then
    return 1
  else
    return 2) := by rfl

-- Test: Three-level nested if with mutable variables
example : (Id.run doo
  let mut x := 0
  if true then
    if true then
      if false then
        x := 1
      else
        x := 2
    else
      x := 3
  else
    x := 4
  return x)
= (Id.run do
  let mut x := 0
  if true then
    if true then
      if false then
        x := 1
      else
        x := 2
    else
      x := 3
  else
    x := 4
  return x) := by rfl

-- Test: Mutable variable used in condition
example : (Id.run doo
  let mut x := 5
  if x > 3 then
    x := x * 2
  else
    x := x + 1
  return x)
= (Id.run do
  let mut x := 5
  if x > 3 then
    x := x * 2
  else
    x := x + 1
  return x) := by rfl

-- Test: Multiple monadic binds in sequence
example : (Id.run doo
  let a ← pure 1
  let b ← pure (a + 1)
  let c ← pure (a + b)
  return (a + b + c))
= (Id.run do
  let a ← pure 1
  let b ← pure (a + 1)
  let c ← pure (a + b)
  return (a + b + c)) := by rfl

-- Test: Mutable bind in if condition position
example : (Id.run doo
  let mut x := 0
  let y ← if x == 0 then pure 1 else pure 2
  x := y
  return x)
= (Id.run do
  let mut x := 0
  let y ← if x == 0 then pure 1 else pure 2
  x := y
  return x) := by rfl

-- Test: Empty else branch behavior
example : (Id.run doo
  let mut x := 5
  if false then
    x := 10
  return x)
= (Id.run do
  let mut x := 5
  if false then
    x := 10
  return x) := by rfl

-- Test: Nested doo with if and early return
example : (Id.run doo
  let mut x := 10
  let y ← do
    if h : true then
      x := x + 3
      pure 42
    else
      return 13
  return x + y)
= (Id.run do
  let mut x := 10
  let y ← do
    if h : true then
      x := x + 3
      pure 42
    else
      return 13
  return x + y) := by rfl

-- Test: ifCondLet and else if
example : (Id.run doo
  let mut x := 0
  if let false := not true then
    x := 10
  else if let 0 ← pure 42 then
    return 42
  else
    x := 3
  x := x + 13
  return x)
= (Id.run do
  let mut x := 0
  if let false := not true then
    x := 10
  else if let 0 ← pure 42 then
    return 42
  else
    x := 3
  x := x + 13
  return x) := by rfl

-- Test: elabToSyntax and postponement
/--
error: Invalid match expression: The type of pattern variable 'y' contains metavariables:
  ?m.13
-/
#guard_msgs (error) in
example := Id.run do
  let mut x := 0 -- We should not get an error that fixed elaborator 0 was not registered
  if let some y := none then
    pure 1
  else
    pure 2

-- Test: For loops with break, continue and return
example :
  (Id.run doo
  let mut x := 42
  for i in [0:100].toList do
    if i = 40 then return x
    if i > 20 then x := x + 3; break
    if i < 20 then x := x * 2; continue
    x := x + i
  x := x + 13
  x := x + 13
  return x)
= (Id.run do
  let mut x := 42
  for i in [0:100].toList do
    if i = 40 then return x
    if i > 20 then x := x + 3; break
    if i < 20 then x := x * 2; continue
    x := x + i
  x := x + 13
  x := x + 13
  return x) := by rfl

-- set_option trace.Meta.synthInstance true in
set_option trace.Elab.do true in
-- Test: Nested for loops with break, continue and return
example :
  (Id.run doo
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] do
    x := x + i
    for j in [i:10].toList do
      if j < 5 then z := z + j
      if j > 8 then return 42
      if j < 3 then continue
      if j > 6 then break
      z := z + i
  return x + y + z)
= (Id.run do
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] do
    x := x + i
    for j in [i:10].toList do
      if j < 5 then z := z + j
      if j > 8 then return 42
      if j < 3 then continue
      if j > 6 then break
      z := z + i
  return x + y + z) := by rfl

-- Test: Try/catch
example {try_ : Except String Nat} {catch_ : String → Except String Nat} :
  (Id.run <| ExceptT.run (ε:=String) doo
  let x ←
    try try_ -- TODO: investigate why we can't put it on the same line
    catch e => catch_ e
  return x + 23)
= (Id.run <| ExceptT.run (ε:=String) do
  let x ← try try_ catch e => catch_ e
  return x + 23) := by simp

-- Test: Try/catch with throw in continuation (i.e., `tryCatch` is non-algebraic)
example :
  (Id.run <| ExceptT.run (ε:=String) doo
  try pure ()
  catch e => pure ()
  throw (α:=Nat) "error")
= throw (α:=Nat) "error" := by rfl

set_option trace.Elab.do true in
set_option backward.do.legacy false in
#check (Id.run <| ExceptT.run (ε:=String) do
  let mut x := 0
  try
    if true then
      x := 10
      throw "error"
      return ()
    else
      x := 5
  catch e =>
    x := x + 1)

#check (Id.run <| ExceptT.run (ε:=String) do
  let mut x := 0
  try
    if true then
      throw "error"
      return ()
    else
      pure ()
  catch e =>
    pure ())

-- Try/catch with reassignment
example :
  (Id.run <| ExceptT.run (ε:=String) doo
  let mut x := 0
  try
    if true then
      x := 10
      throw "error"
    else
      x := 5
  catch e =>
    x := x + 1
  return x)
= (Id.run <| ExceptT.run (ε:=String) do
  let mut x := 0
  try
    if true then
      x := 10
      throw "error"
    else
      x := 5
  catch e =>
    x := x + 1
  return x) := by rfl

#check (Id.run <| StateT.run' (σ := Nat) (s := 42) <| ExceptT.run (ε:=String) doo
  try
    pure ()
  finally
    set 0
  get)

-- Try/finally
example {s} :
  (Id.run <| StateT.run' (σ := Nat) (s := s) <| ExceptT.run (ε:=String) doo
  try
    e
  finally
    set 0
  get)
= (Id.run <| StateT.run' (σ := Nat) (s := s) <| ExceptT.run (ε:=String) do
  try
    e
  finally
    set 0
  get) := by simp

set_option trace.Elab.do true in
--set_option trace.Meta.isDefEq true in
-- Try/catch with return, break and continue
example :
  let f n :=
      (Id.run <| ExceptT.run (ε:=String) doo
      let mut x := 0
      for i in [n:n+10].toList do
        try
          if i = 5 then return x
          if i = 15 then break
          if i = 25 then continue
          if i = 35 then throw "error"
          x := x + i
        catch _ =>
          x := x + 1
      return x)
    = (Id.run <| ExceptT.run (ε:=String) do
      let mut x := 0
      for i in [n:n+10].toList do
        try
          if i = 5 then return x
          if i = 15 then break
          if i = 25 then continue
          if i = 35 then throw "error"
          x := x + i
        catch _ =>
          x := x + 1
      return x)
  f 0 ∧ f 10 ∧ f 20 ∧ f 30 ∧ f 31 ∧ f 45 ∧ f 1023948 := by trivial

-- Try/catch with return and continue
example :
  let f n :=
      (Id.run <| ExceptT.run (ε:=String) doo
      let mut x := 0
      for i in [n:n+10].toList do
        try
          if i = 5 then return x
          if i = 25 then continue
          if i = 35 then throw "error"
          x := x + i
        catch _ =>
          x := x + 1
      return x)
    = (Id.run <| ExceptT.run (ε:=String) do
      let mut x := 0
      for i in [n:n+10].toList do
        try
          if i = 5 then return x
          if i = 25 then continue
          if i = 35 then throw "error"
          x := x + i
        catch _ =>
          x := x + 1
      return x)
  f 0 ∧ f 10 ∧ f 20 ∧ f 30 ∧ f 31 ∧ f 45 ∧ f 1023948 := by trivial

-- Try/catch with return and break
example :
  let f n :=
      (Id.run <| ExceptT.run (ε:=String) doo
      let mut x := 0
      for i in [n:n+10].toList do
        try
          if i = 5 then return x
          if i = 15 then break
          if i = 35 then throw "error"
          x := x + i
        catch _ =>
          x := x + 1
      return x)
    = (Id.run <| ExceptT.run (ε:=String) do
      let mut x := 0
      for i in [n:n+10].toList do
        try
          if i = 5 then return x
          if i = 15 then break
          if i = 35 then throw "error"
          x := x + i
        catch _ =>
          x := x + 1
      return x)
  f 0 ∧ f 10 ∧ f 20 ∧ f 30 ∧ f 31 ∧ f 45 ∧ f 1023948 := by trivial

-- Try/catch with break
example :
  let f n :=
      (Id.run <| ExceptT.run (ε:=String) doo
      let mut x := 0
      for i in [n:n+10].toList do
        try
          if i = 15 then break
          if i = 35 then throw "error"
          x := x + i
        catch _ =>
          x := x + 1
      return x)
    = (Id.run <| ExceptT.run (ε:=String) do
      let mut x := 0
      for i in [n:n+10].toList do
        try
          if i = 15 then break
          if i = 35 then throw "error"
          x := x + i
        catch _ =>
          x := x + 1
      return x)
  f 0 ∧ f 10 ∧ f 20 ∧ f 30 ∧ f 31 ∧ f 45 ∧ f 1023948 := by trivial

-- Parallel for loops
set_option backward.do.legacy false in
example :
  let f n m :=
    (Id.run doo
      let mut a := 0
      for h : x in [1,2,3], y in [0:n], z in [0:m] do
        have : x < 5 := by grind
        a := a + x + y + z
      return a)
    = (Id.run do
      let mut a := 0
      for h : x in [1,2,3], y in [0:n], z in [0:m] do
        have : x < 5 := by grind
        a := a + x + y + z
      return a)
  f 3 3 ∧ f 1 4 ∧ f 4 2 ∧ f 5 5 := by trivial

set_option backward.do.legacy false in
example {f : Nat → Nat → Id Unit} :
  (Id.run do f (← e₁) (← e₂); es)
  =
  (Id.run do let x ← e₁; let y ← e₂; f x y; es)
  := by rfl

set_option backward.do.legacy false in
example {g : Nat → Id Unit} {h : Nat → Id Nat} :
  (Id.run do let x := g (← h (← e₁)); es)
  =
  (Id.run do let x ← e₁; let y ← h x; g y; es)
  := by rfl


/-!
Postponing Monad instance resolution appropriately
-/

/--
error: typeclass instance problem is stuck
  Pure ?m.8

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `Pure` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs (error) in
example := doo return 42
/--
error: typeclass instance problem is stuck
  Bind ?m.23

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `Bind` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs (error) in
example := doo let x <- ?z; ?y
/-
error: typeclass instance problem is stuck
  Pure ?m.12

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `Pure` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
-- #guard_msgs (error) in
-- example := do return 42
/-
error: typeclass instance problem is stuck
  Bind ?m.16

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `Bind` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
--#guard_msgs (error) in
-- example := do let x <- ?z; ?y

-- This tests that inferred types are correctly propagated outwards.
example {e : Id Nat} := doo if true then e else pure 13
-- We do want to be able to `#check` the following example (including the last `pure`) without an
-- expected monad, ...
#check doo let mut x : Nat := 0; if true then {x := x + 1} else {pure ()}; pure x
-- As well as fully resolve all instances in the following example where the expected monad is
-- known. The next example wouldn't work without `Id.run`.
set_option trace.Elab.do true in
example := Id.run doo let mut x : Nat := 0; if true then {x := x + 1} else {pure ()}; pure x

/-- error: mutable variable `x` cannot be shadowed -/
#guard_msgs (error) in
example := (Id.run doo let mut x := 42; x := x - 7; let x := x + 4; return x + 13)

/--
error: Application type mismatch: The argument
  true
has type
  Bool
but is expected to have type
  PUnit
in the application
  pure true
-/
#guard_msgs (error) in
example := (Id.run doo pure true; pure ())

/--
error: Application type mismatch: The argument
  true
has type
  Bool
but is expected to have type
  PUnit
in the application
  pure true
---
error: Application type mismatch: The argument
  false
has type
  Bool
but is expected to have type
  PUnit
in the application
  pure false
-/
#guard_msgs (error) in
example := (Id.run doo if true then {pure true} else {pure false}; pure ())

/--
error: Application type mismatch: The argument
  false
has type
  Bool
but is expected to have type
  PUnit
in the application
  pure false
-/
#guard_msgs (error) in
example := (Id.run doo if true then {pure ()} else {pure false}; pure ())

-- Additional error tests

/--
error: Variable `foo` cannot be mutated. Only variables declared using `let mut` can be mutated.
      If you did not intend to mutate but define `foo`, consider using `let foo` instead
-/
#guard_msgs (error) in
example := (Id.run doo foo := 42; pure ())

/-- error: mutable variable `x` cannot be shadowed -/
#guard_msgs (error) in
example := (Id.run doo let mut x := 1; if true then {let mut x := 2; pure ()} else {pure ()}; pure x)

-- Regression test cases of what's currently broken in the do elaborator:
example : Unit := (Id.run do  let n ← if true then pure 3 else pure 42)
example : Unit := (Id.run doo let n ← if true then pure 3 else pure 42)
example := (Id.run do  let mut x := 0; x ← return 10)
example := (Id.run doo let mut x := 0; x ← return 10)

set_option diagnostics true in
/--
info: have x := 0;
let y := 0;
have __do_jp := fun __r x_1 => pure (x_1 + y);
if true = true then pure 3
else
  have x := x + 5;
  let y := 3;
  __do_jp PUnit.unit x : ?m Nat
-/
#guard_msgs (info) in
#check doo
  let mut x : Nat := 0
  let y := 0
  if true then
    return 3
  else
    x := x + 5
    let y := 3
  return x + y

/--
info: have x := 0;
let y := 0;
have __do_jp := fun __r x_1 => pure (x_1 + y);
if true = true then
  have x := x + 7;
  let y := 3;
  __do_jp PUnit.unit x
else
  have x := x + 5;
  __do_jp PUnit.unit x : ?m Nat
-/
#guard_msgs (info) in
#check doo
  let mut x : Nat := 0
  let y := 0
  if true then
    x := x + 7
    let y := 3
  else
    x := x + 5
  return x + y


set_option trace.Elab.do true in
/--
trace: [Elab.do] have x := 42;
    do
    let __s ←
      forIn [1, 2, 3] (none, x) fun i __s =>
          let x_1 := __s.snd;
          have __do_jp := fun __r x_2 =>
            have __do_jp := fun __r_1 x_3 =>
              have __do_jp := fun __r_2 x_4 =>
                have x := x_4 + i;
                pure (ForInStep.yield (none, x));
              if x_3 < 20 then
                have x := x_3 * 2;
                pure (ForInStep.done (none, x))
              else __do_jp PUnit.unit x_3;
            if x_2 > 10 then
              have x := x_2 + 3;
              pure (ForInStep.yield (none, x))
            else __do_jp PUnit.unit x_2;
          if x_1 = 3 then pure (ForInStep.done (some x_1, x_1)) else __do_jp PUnit.unit x_1
    let __r : Option ?m.182 := __s.fst
    let x_1 : ?m.182 := __s.snd
    match __r with
      | some r => pure r
      | none =>
        have x_2 := x_1 + 13;
        have x_3 := x_2 + 13;
        have x_4 := x_3 + 13;
        have x := x_4 + 13;
        pure x
-/
#guard_msgs in
example := Id.run doo
  let mut x := 42
  for i in [1,2,3] do
    if x = 3 then return x
    if x > 10 then x := x + 3; continue
    if x < 20 then x := x * 2; break
    x := x + i
  x := x + 13
  x := x + 13
  x := x + 13
  x := x + 13
  return x

set_option trace.Elab.do true in
example := Id.run doo
  let mut x := 42
  return x

example : Id Nat := do
  let x := 42
  x + ?x
where finally
case x => exact 13

section Issue11337

structure Foo (n : Nat) where
  (l : List Nat)
  (h : n = n)

def foo (n : Nat) : MetaM Unit := do
  let mut result : Foo n := ⟨[7], rfl⟩
  trace[Meta.Tactic.simp] "{result.l}"
  result := ⟨List.range n, rfl⟩
  trace[Meta.Tactic.simp] "{result.l}"
  match n with
  | _ => trace[Meta.Tactic.simp] "{result.l}"

set_option trace.Meta.Tactic.simp true
/--
trace: [Meta.Tactic.simp] [7]
[Meta.Tactic.simp] [0, 1, 2, 3, 4]
[Meta.Tactic.simp] [0, 1, 2, 3, 4]
-/
#guard_msgs in
run_meta do
  foo 5

set_option backward.do.legacy false in
def bar (n : Nat) : MetaM (List Nat) := doo
  let mut result : Foo n := ⟨[7], rfl⟩
  trace[Meta.Tactic.simp] "{result.l}"
  result := ⟨List.range n, rfl⟩
  trace[Meta.Tactic.simp] "{result.l}"
  -- match (motive := ∀ _, MetaM (List Nat)) n with
  have result2 : Foo n := ⟨[7], rfl⟩
  match (generalizing := false) n with
  | 0   => pure (); result := ⟨[10], rfl⟩
  | n+1 => result := ⟨[6], rfl⟩
  trace[Meta.Tactic.simp] "{result.l}"
  return result.l

example (n : Nat) : Foo n :=
  have result2 : Foo n := ⟨[7], rfl⟩
  match (generalizing := false) h : n with
  | 0   => ⟨[10], rfl⟩
  | n+1 => ⟨[6], rfl⟩

set_option trace.Meta.Tactic.simp true
/--
trace: [Meta.Tactic.simp] [7]
[Meta.Tactic.simp] []
[Meta.Tactic.simp] [10]
[Meta.Tactic.simp] [7]
[Meta.Tactic.simp] [0, 1, 2, 3, 4]
[Meta.Tactic.simp] [6]
-/
#guard_msgs in
run_meta do
  discard <| bar 0
  discard <| bar 5

end Issue11337
