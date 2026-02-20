import Lean
import Lake

open Lean Parser Meta Elab Do

set_option linter.unusedVariables false
set_option backward.do.legacy false

/-!
Miscellaneous tests for the new `do` elaborator.
Many of these are extracted from our code base.
-/

-- Test: Try/catch with let mut and match
#check Id.run <| ExceptT.run (ε:=String) (α := Fin 17) do
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

-- Regression test cases of what's broken in the legacy do elaborator:
example : Unit := (Id.run do  let n ← if true then pure 3 else pure 42)
example : Unit := (Id.run do let n ← if true then pure 3 else pure 42)
example := (Id.run do  let mut x := 0; x ← return 10)
example := (Id.run do let mut x := 0; x ← return 10)

-- Another complicated `match` that would need to generalize the join point type if it was dependent
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
    pure ⟨r + 1, by grind⟩

-- Full-blown match + try/catch, early return and break/continue
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

/--
error: The `do` elaborator does not support custom motives.
If you want a dependent match, try `(dependent := true)`.
If you want to provide an expected type, do so via type ascription on the bind.
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

-- Test: elabToSyntax and postponement
/--
error: Invalid match expression: The type of pattern variable 'y' contains metavariables:
  ?m.13
-/
#guard_msgs (error) in
example := Id.run do
  let mut x := 0
  if let some y := none then
    pure 1
  else
    pure 2
/--
error: typeclass instance problem is stuck
  Pure ?m.8

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `Pure` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs (error) in
example := do return 42
/--
error: typeclass instance problem is stuck
  Bind ?m.23

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `Bind` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs (error) in
example := do let x ← ?z; ?y

-- This tests that inferred types are correctly propagated outwards.
example {e : Id Nat} := do if true then e else pure 13
-- We do want to be able to `#check` the following example (including the last `pure`) without an
-- expected monad, ...
#check do let mut x : Nat := 0; if true then {x := x + 1} else {pure ()}; pure x
-- As well as fully resolve all instances in the following example where the expected monad is
-- known. The next example wouldn't work without `Id.run`.
example := Id.run do let mut x : Nat := 0; if true then {x := x + 1} else {pure ()}; pure x

/-- error: mutable variable `x` cannot be shadowed -/
#guard_msgs (error) in
example := (Id.run do let mut x := 42; x := x - 7; let x := x + 4; return x + 13)

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
example := (Id.run do pure true; pure ())

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
example := (Id.run do if true then {pure true} else {pure false}; pure ())

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
example := (Id.run do if true then {pure ()} else {pure false}; pure ())

-- Additional error tests

/--
error: Variable `foo` cannot be mutated. Only variables declared using `let mut` can be mutated.
      If you did not intend to mutate but define `foo`, consider using `let foo` instead
-/
#guard_msgs (error) in
example := (Id.run do foo := 42; pure ())

/-- error: mutable variable `x` cannot be shadowed -/
#guard_msgs (error) in
example := (Id.run do let mut x := 1; if true then {let mut x := 2; pure ()} else {pure ()}; pure x)

-- Test that we inline join points if they are just used once
set_option trace.Elab.do true in
/--
trace: [Elab.do] let x := 42;
    do
    let __s ←
      forIn [1, 2, 3] (none, x) fun i __s =>
          let x := __s.snd;
          if x = 3 then pure (ForInStep.done (some x, x))
          else
            if x > 10 then
              let x := x + 3;
              pure (ForInStep.yield (none, x))
            else
              if x < 20 then
                let x := x * 2;
                pure (ForInStep.done (none, x))
              else
                let x := x + i;
                pure (ForInStep.yield (none, x))
    let __r : Option ?m.182 := __s.fst
    let x : ?m.182 := __s.snd
    match __r with
      | some r => pure r
      | none =>
        let x := x + 13;
        let x := x + 13;
        let x := x + 13;
        let x := x + 13;
        pure x
-/
#guard_msgs in
example := Id.run do
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

-- Test that we pass around all mutable variables that have been reassigned
/--
info: (let w := 23;
  let x := 42;
  let y := 0;
  let z := 1;
  do
  let __s ←
    forIn [1, 2, 3] (x, y, z) fun i __s =>
        let x := __s.fst;
        let __s_1 := __s.snd;
        let y := __s_1.fst;
        let z := __s_1.snd;
        if x < 20 then
          let y := y - 2;
          pure (ForInStep.done (x, y, z))
        else
          have __do_jp := fun __r z =>
            if x > 10 then
              let x := x + 3;
              pure (ForInStep.yield (x, y, z))
            else
              let x := x + i;
              pure (ForInStep.yield (x, y, z));
          if x = 3 then
            let z := z + i;
            __do_jp PUnit.unit z
          else __do_jp PUnit.unit z
  let x : Nat := __s.fst
  let __s : Nat × Nat := __s.snd
  let y : Nat := __s.fst
  let z : Nat := __s.snd
  pure (w + x + y + z)).run : Nat
-/
#guard_msgs (info) in
#check Id.run do
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

namespace Repros

example {α} (mask : Array Bool) (xs : Array α) : Array α := Id.run do
  let mut ys := #[]
  for b in mask, x in xs do
    if b then ys := ys.push x
  return ys

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

-- Test that we can elaborate match RHS without knowing the continuation's result type (`MVarId`).
example (subgoals : List (Option Expr × MVarId)) : MetaM Unit :=
  discard <| subgoals.mapM fun ⟨e, mv⟩ ↦ do
    let mvar' ← match e with | none => pure mv | some _ => pure mv
    mvar'.withContext <| mvar'.assign Nat.mkType

-- test case doLetElse. We reject this because we don't support dependent match.
/--
error: Type mismatch
  y
has type
  Fin 3
but is expected to have type
  Fin (x + 1)
-/
#guard_msgs (error) in
example (x : Nat) : IO (Fin (x + 1)) := do
  let 2 := x | return 0
  -- the pattern match performed a substitution
  let y : Fin 3 := ⟨1, by decide⟩
  return y

-- Test new semantics of `let pat := rhs | otherwise`:
/-- info: "ok" -/
#guard_msgs in
#eval Id.run do
  let mut x := 0
  let y <- do
    let true := false | do x := x + 3; pure 0
    x := x + 100
    return "unreachable"
  if x + y < 23 then pure "ok" else pure "wrong"

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

example (cache : Std.HashMap (Nat × Nat) Bool) : Bool := Id.run do
  let key := ⟨1, 2⟩
  match cache[key]? with
  | some r => return true
  | none => pure ()
  let := cache.contains key
  return false

end Repros


namespace DeleteBeforeMerging

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

example (declName : Name) (x : Bool) (f : String → MetaM Bool) : MetaM Unit := do
  let res ← match x with | _ => throwError m!"`{.ofConstName declName}` has no docstring"
  let _ ← f res
  throwError "No metadata satisfied the predicate"

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

section Array

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
