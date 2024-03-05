import Lean.Elab.Command
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Meta
import Lean.Meta.CheckTactic
import Lean.Parser.Term

open Lean Meta Elab Term Command CheckTactic

/-
This module defines a term generation and testing framework that
checks whether generated terms have a specified normal form.  It
is defined in the `Lean.Test.NormalForms` namespace.

To use it, you need to define a few things:

1. a new datatype for representing terms in the language
2. a data type for representing types
3. a function for computing the type from the term
4. a function for rendering the term into Lean syntax
5. an evaluation function for producing the expected normal form from the term syntax
6. a list of variable generators for generating variables with different types in the language
7. a list of operators `Op` for building up terms in the language.

Once this is done, you can pass this information into
`testNormalForms`.
-/
namespace Lean.Test.NormalForms

-- | A `Op` is a first order operation for generating values with a given type.
structure Op (tp : Type) (val : Type) where
  args : Array tp
  result : tp
  apply : Array val → val
 deriving Inhabited

def mkOp (args : List tp) (result : tp) (apply : Array val → val) : Op tp val :=
  { apply := apply, args := args.toArray, result }

def Op.map (op : Op x val) (f : x → y) : Op y val :=
  { apply := op.apply, args := op.args.map f, result := f op.result }

/--
Contextual information needed to generate terms.
-/
structure GenCtx (term : Type) where
  -- Maps type indices to operator for corresponding type.
  -- Types use type indices.
  ops : Array (Array (Op Nat term))
  /-- Maps type indices to variables for that type. -/
  vars : Array (Array term)
  /- Operators to use for patterns at top of terms -/
  topOps : Array (Op Nat term)
  /- Returns the expected reduction of a term -/
  expected : term → term
  /- Predicate that returns true if terms are equal-/
  eq : term → term → Bool
  /-- Maximum term size -/
  maxTermSize : Nat
  /-- Maximum depth of terms -/
  maxDepth : Nat
  /-- Maximum number of variables -/
  maxVarCount : Nat
  /- Local context variables defined in -/
  lctx : LocalContext
  /- Local instances for variables -/
  linst : LocalInstances

namespace GenCtx

/-- `var ctx tp idx` returns a term denoting `i`th variable with type `tp`. -/
def var (ctx : GenCtx term) (tp : Nat) (idx : Nat) : Option term :=
  if g : tp < ctx.vars.size then
    let a := ctx.vars[tp]'g
    if h : idx < a.size then
      some (a[idx]'h)
    else
      none
  else
    none

end GenCtx

/-- An operator together with a set of terms to apply to it. -/
structure PartialApp (term : Type) where
  /-- Operator to generate -/
  op : Op Nat term
  /-- Terms constructed so far -/
  terms : Array term

namespace PartialApp

def fromOp (op : Op Nat term) : PartialApp term :=
  { op, terms := .mkEmpty op.args.size }

end PartialApp

/--
A partial term contains the initial part of a term as constructed from a
left-to-right preorder traversal.

It stores additional information needed to ensure the ultimate term satisfies
the generation constraints on term size and number of variables.

The operations for constructing this ensures the term is well-formed
with respect to the signature and is not a complete term.
-/
structure PartialTerm (term : Type) where
  /-- Stack of partially built term (must be non-empty) -/
  termStack : Array (PartialApp term)
  /-- Maximum number of additional operations that may be added. -/
  remTermSize : Nat
  /-- Variables used with type index. -/
  usedVars : Array Nat
  deriving Inhabited

namespace PartialTerm

/--
Create an initial partial term from an operator.

If the operator is a constant, then this just returns a complete terms.
-/
def init (maxTermSize : Nat) (maxDepth : Nat) (op : Op Nat term) : term ⊕ PartialTerm term :=
  if op.args.isEmpty then
    .inl (op.apply #[])
  else
    .inr {
      termStack := #[PartialApp.fromOp op],
      remTermSize := maxTermSize - (1 + op.args.size),
      usedVars := #[]
    }

partial def push (p : PartialTerm term) (t : term) : term ⊕ PartialTerm term :=
  match p.termStack.back? with
  | none => .inl t
  | some { op, terms } =>
    let p := { p with termStack := p.termStack.pop }
    let terms := terms.push t
    if terms.size = op.args.size then
      let v := op.apply terms
      push p v
    else
      .inr { p with termStack := p.termStack.push { op, terms } }

/-- Push an operator to the stack -/
def pushOp (p : PartialTerm term) (op : Op Nat term) : PartialTerm term :=
  { termStack   := p.termStack.push (.fromOp op)
    remTermSize := p.remTermSize - op.args.size,
    usedVars := p.usedVars
  }

end PartialTerm

/--
Term generator
-/
structure TermGen (term : Type) where
  sofar : Array term := #[]
  pending : Array (PartialTerm term) := #[]
  deriving Inhabited

namespace TermGen

/-- Return true if generator will return no more terms. -/
def isEmpty (s: TermGen term) : Bool := s.sofar.isEmpty && s.pending.isEmpty

def pop (s : TermGen term) : Option (Nat × PartialTerm term × TermGen term) :=
  if s.pending.isEmpty then
    .none
  else
    let { sofar, pending } := s
    let next := pending.back
    let pending := pending.pop
    match next.termStack.back? with
    | none =>
      panic! "Term stack empty"
    | some app =>
      let tp := app.op.args[app.terms.size]!
      some (tp, next, { sofar, pending })

def add (gen : TermGen term)  (val : term ⊕ PartialTerm term) : TermGen term :=
  let { sofar, pending } := gen
  match val with
  | .inl v =>  { sofar := sofar.push v, pending }
  | .inr p => { sofar, pending := pending.push p }

/-
`push s next v` adds the result of `next.push v` to the state.

This only adds terms that are irreducible.
-/
def push (gen : TermGen term) (ctx : GenCtx term) (next : PartialTerm term) (v : term) : TermGen term :=
  let exp := ctx.expected v
  if ctx.eq exp v then
    gen.add (next.push v)
  else
    gen

def pushOp (gen : TermGen term) (ctx : GenCtx term) (next : PartialTerm term) (op : Op Nat term) :=
  if op.args.isEmpty then
    gen.push ctx next (op.apply #[])
  else if op.args.size ≤ next.remTermSize ∧ next.termStack.size + 1 < ctx.maxDepth then
    { gen with pending := gen.pending.push (next.pushOp op) }
  else
    gen

/-- Create state that will explore all terms in context -/
def addOpInstances (s : TermGen term) (ctx : GenCtx term) (op : Op Nat term) : TermGen term :=
  s.add (PartialTerm.init ctx.maxTermSize ctx.maxDepth op)

/-- Create state that will explore all terms in context -/
def init (ctx : GenCtx term) : TermGen term :=
  ctx.topOps.foldl (init := {}) (·.addOpInstances ctx ·)

end TermGen

/--
Generate terms until we reach the limit.
-/
partial
def generateTerms
    (ctx : GenCtx term)
    (gen : TermGen term)
    (limit : Nat := 0) :
    Array term × TermGen term :=
  if limit > 0 ∧ gen.sofar.size ≥ limit then
    -- Stop if we hit term limit
    (gen.sofar, { gen with sofar := #[] })
  else
    match gen.pop with
    | none =>
      -- stop when out of terms
      (gen.sofar, { gen with sofar := #[] })
    | some (tp, next, gen) =>
      -- Add previously used variables to term
      let addVar (next : PartialTerm term) (i : Nat) (gen : TermGen term) : TermGen term :=
            -- If the previous variable i matches type, then add it to generator
            if next.usedVars[i]! = tp then
              match ctx.var tp i with
              | some v => gen.push ctx next v
              | none => gen
            else
              gen
      let s := next.usedVars.size.fold (init := gen) (addVar next)
      let s :=
        let var := next.usedVars.size
        if var < ctx.maxVarCount then
          let next := { next with usedVars := next.usedVars.push tp }
          addVar next var s
        else
          s
      generateTerms ctx (ctx.ops[tp]!.foldl (init := s) (·.pushOp ctx next ·)) limit

/-
`addScopeVariables` extends the local context and instances with a copy of the
variables in the scope (which must be non-empty).
-/
def addScopeVariables (lctx : LocalContext) (linst : LocalInstances) (scope : Scope) (idx : Nat) :
    CoreM (LocalContext × LocalInstances × Ident) := do
  let act := Term.elabBindersEx scope.varDecls fun vars => do pure (vars, ← (read : MetaM Meta.Context))
  let mctx := { lctx := lctx, localInstances := linst }
  let (((vars, mctx), _tstate), _mstate) ← act |>.run |>.run mctx
  if vars.isEmpty then
    throwError "No variables declared"
  let fv := vars[0]!.snd |>.fvarId!
  let rec drop (nm : Name) :=
        match nm with
        | .str .anonymous s => pure (.str .anonymous s!"{s}{idx}")
        | .str nm _ => drop nm
        | .num nm _ => drop nm
        | .anonymous => throwError "Anonymous variable declared."
  let nm ← drop (mctx.lctx.get! fv |>.userName)
  let lctx := mctx.lctx.setUserName fv nm
  pure (lctx, mctx.localInstances, mkIdent nm)

def addVariables (cmdCtx : Command.Context) (cmdState : Command.State) (lctx : LocalContext) (linst : LocalInstances) (n : Nat) (cmd : Command) :
    CoreM (LocalContext × LocalInstances × Array Ident) := do
  let (_, s) ←  elabCommand cmd.raw |>.run cmdCtx |>.run cmdState
  let scope := s.scopes.head!
  Nat.foldM (n := n) (init := (lctx, linst, .mkEmpty n)) fun i (lctx, linst, a) => do
    let (lctx, linst, ident) ← addScopeVariables lctx linst scope i
    pure (lctx, linst, a.push ident)

structure GenStats where
  maxTermSize : Nat := 9
  maxDepth : Nat := 3
  maxVarCount : Nat := 3


structure VarDecl (tp : Type) where
  idx : Nat
  ident : TSyntax `ident
  type : tp
  deriving Inhabited, Repr

instance : BEq (VarDecl tp) where
  beq x y := x.idx == y.idx

instance : Hashable (VarDecl tp) where
  hash v := hash v.idx

/--

-/
class GenTerm (term : Type) (type : outParam Type) extends BEq term where
  mkVar : VarDecl type → term
  render : term → TermElabM Term

def mkCtx [BEq tp] [Hashable tp] [BEq term]
    (types : Array tp)
    (ops : List (Op tp term))
    (varGen : List (tp × CoreM Command))
    (mkVar : VarDecl tp → term)
    (expected : term → term)
    (stats : GenStats)
    (topOps : List (Op tp term) := ops) : CommandElabM (GenCtx term) := do
  let typeMap : HashMap tp Nat := Nat.fold (n := types.size) (init := {}) fun i s =>
        if p : i < types.size then
          s.insert types[i] i
        else
          s
  let typeFn (t : tp) := typeMap.findD t 0
  let addOp (a : Array (Array (Op Nat term))) (op : Op tp term) :=
        let op := op.map typeFn
        a.modify op.result (·.push op)
  let init := Array.ofFn (n := types.size) (fun _ => #[])
  let ops := ops.foldl (init := init) addOp
  let ops := ops.map (·.reverse)
  let topOps := topOps.toArray.map (·.map typeFn)
  let (lctx, linst, vars) ← liftCoreM do
    let coreCtx ← read
    let coreState ← get
    let fileName := coreCtx.fileName
    let fileMap  := coreCtx.fileMap
    let env := coreState.env
    let maxRecDepth := coreCtx.maxRecDepth
    let cmdCtx : Command.Context := { fileName, fileMap, tacticCache? := none }
    let cmdState : Command.State := { env, maxRecDepth }
    let addVars (p : LocalContext × LocalInstances × Array (Array term))
                (q : tp × CoreM Command) :
                CoreM (LocalContext × LocalInstances × _) := do
          let (lctx, linst, a) := p
          let (type, gen) := q
          let cmd ← gen
          let (lctx, linst, vars) ← addVariables cmdCtx cmdState lctx linst stats.maxVarCount cmd
          let vars := Array.ofFn (n := vars.size) fun j => mkVar { idx := j.val, ident := vars[j], type }
          let type := typeFn type
          pure (lctx, linst, a.modify type (fun _ => vars))
    let vars := Array.ofFn (n := types.size) fun _ => #[]
    varGen.foldlM (init := ({}, {}, vars)) addVars
  let maxTermSize : Nat := stats.maxTermSize
  let maxDepth : Nat := stats.maxDepth
  let maxVarCount : Nat := stats.maxVarCount
  pure { ops, vars, expected := @expected, eq := BEq.beq, topOps, maxTermSize, maxDepth, maxVarCount, lctx, linst }

/-
runTest
-/
def runTest (render : term → TermElabM Syntax.Term) (simp : term → term) (tac : Syntax.Tactic) (tm : term) : TermElabM Unit := do
  withoutModifyingEnv $ do
    let res := simp tm
    let t ← render tm
    let exp ← render res
    let u ← Lean.Elab.Term.elabTerm t none
    let type ← inferType u
    let checkGoalType ← mkCheckGoalType u type
    let expTerm ← Lean.Elab.Term.elabTerm exp (some type)
    let mvar ← mkFreshExprMVar (.some checkGoalType)
    let (goals, _) ← Lean.Elab.runTactic mvar.mvarId! tac.raw
    match goals with
    | [next] => do
      let (val, _, _) ← matchCheckGoalType (←next.getType)
      if !(← Meta.withReducible <| isDefEq val expTerm) then
        logError m!"{indentExpr u} reduces to{indentExpr val}\nbut is expected to reduce to {indentExpr expTerm}"
    | [] =>
      logError m!"{tac} closed goal, but is expected to reduce to {indentExpr expTerm}."
    | _ =>
      logError m!"{tac} produced multiple goals, but is expected to reduce to {indentExpr expTerm}."

/-
Create core context for running tactic tests in.
-/
private def mkCoreContext (ctx : Command.Context) (options : Options) (maxRecDepth : Nat) (initHeartbeats : Nat) : Core.Context :=
  { fileName       := ctx.fileName
    fileMap        := ctx.fileMap
    options,
    currRecDepth   := ctx.currRecDepth
    maxRecDepth,
    ref            := ctx.ref
    initHeartbeats,
    currMacroScope := ctx.currMacroScope }

/-- Runs term elaborator in base context. -/
def runTermElabM (cctx : Core.Context) (cstate : Core.State) (mctx : Meta.Context) (act : TermElabM Unit)
    : BaseIO (Except Exception MessageLog) := do
  let r ← act.run |>.run mctx |>.run cctx cstate |>.toBaseIO
  match r with
  | .error e =>
    pure (.error e)
  | .ok ((((), _termS), _metaS), coreS) =>
    pure (.ok coreS.messages)

/--
Tests that a tactic applied to exhaustively generated terms matches
expectations.

To allow testing consistent treatment of operators on multiple types, the normal
form testing facility is defined using terms over an arbitrary simply-typed
`term` data type that uses types using the `type` parameter.  This
representation should be chosen to make specifying the semantics of the tactic
as simple as possible.

Term must be an instance of the `GenTerm` class so the testing facility knows
how to render user terms into Lean terms.  Additionally, users should provide
operators and variable constructors for building terms up.

`stats` controls parameters on the size of terms generated.
-/
partial def testNormalForms {val type : Type} [BEq type] [Hashable type] [GenTerm val type]
      (types : List type)
      (ops : List (Op type val))
      (vars : List (type × CoreM Command))
      (expected : val → val)
      (stats : GenStats)
      (tac : Option Syntax.Tactic := none)
      (topOps : List (Op type val) := ops)
      (concurrent : Bool := true) : CommandElabM Unit := do

  let tac ← tac.getDM `(tactic|try simp)
  let ctx ← mkCtx (types := types.toArray) (ops := ops) (topOps := topOps) (varGen := vars) (mkVar := GenTerm.mkVar) expected (stats := stats)

  let cmdCtx : Command.Context ← read
  let s ← get
  let maxRecDepth := s.maxRecDepth
  let heartbeats ← IO.getNumHeartbeats
  let options ← getOptions
  -- Create core context for running tests.
  let cctx := mkCoreContext cmdCtx options maxRecDepth heartbeats
  -- Create core context for running tests.
  let cstate : Core.State := {
        env := s.env,
        ngen := s.ngen,
        traceState := s.traceState,
        infoState.enabled := s.infoState.enabled
    }
  -- Meta context setup for variables created by mkCtx
  let mctx : Meta.Context := { lctx := ctx.lctx, localInstances := ctx.linst }
  let gen := TermGen.init ctx
  if concurrent then
    let limit := 800
    let rec loop (gen : TermGen val) (cnt : Nat) (tasks : Array (Task (Except Exception MessageLog))) : BaseIO (Nat × Array (Task _)) := do
      if gen.isEmpty then
        return (cnt, tasks)
      else
        let (terms, gen) := generateTerms ctx gen (limit := limit)
        let runTests := do
              for tm in terms do
                if ← IO.checkCanceled then
                  break
                runTest GenTerm.render expected tac tm
        let t ← runTests |> runTermElabM cctx cstate mctx |>.asTask
        loop gen (cnt + terms.size) (tasks.push t)
    let (cnt, tasks) ←
      profileitM Exception "normal form generation" (←getOptions) (decl := .anonymous) do
        liftIO (loop gen 0 #[])
    trace[Test.normalforms] "generated {cnt} tests running in {tasks.size} threads."
    profileitM Exception "normal form execution" (←getOptions) do
      for i in [0:tasks.size] do
        if ← IO.checkCanceled then
          break
        let act := tasks[i]!
        match act.get with
        | .error e =>
          -- Cancel all tasks after this one
          (tasks |>.toSubarray (start := i+1) |>.forM IO.cancel : BaseIO Unit)
          throw e
        | .ok m =>
          modify fun s => { s with messages := s.messages ++ m }
  else
    let r ← runTermElabM cctx cstate mctx <|
      let (terms, _) := generateTerms ctx gen (limit := 0)
      for tm in terms do
        if ← IO.checkCanceled then
          break
        runTest GenTerm.render expected tac tm
    match r with
    | .error e => throw e
    | .ok m => modify fun s => { s with messages := s.messages ++ m }

builtin_initialize
  registerTraceClass `Test.normalforms

end Lean.Test.NormalForms
