import Lean.Elab.Command
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Meta
import Lean.Meta.CheckTactic
import Lean.Parser.Term

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Command
open Lean.Meta.CheckTactic


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

class HasType (val : Type) (type : outParam Type) where
  typeOf : val → type

class Value (val : Type) where
  render : val → TermElabM Term

/--
Contextual information needed to generate terms.
-/
structure GenCtx (val : Type) where
  -- Maps type indices to operator for corresponding type.
  -- Types use type indices.
  ops : Array (Array (Op Nat val))
  /- Operators to use for patterns at top of terms -/
  topOps : Array (Op Nat val)
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
  /-- Maps type indices to variables for that type. -/
  vars : Array (Array val)

namespace GenCtx

/-- `var ctx tp idx` returns a term denoting `i`th variable with type `tp`. -/
def var (ctx : GenCtx val) (tp : Nat) (idx : Nat) : Option val :=
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
structure Gen (term : Type) where
  sofar : Array term := #[]
  pending : Array (PartialTerm term) := #[]
  deriving Inhabited

namespace Gen

/-- Return true if generator will return no more terms. -/
def isEmpty (s: Gen term) : Bool := s.sofar.isEmpty && s.pending.isEmpty

def pop (s : Gen term) : Option (Nat × PartialTerm term × Gen term) :=
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

/- `push s next v` adds the result of `next.push v` to the state. -/
def push (s : Gen term) (next : PartialTerm term) (v : term) : Gen term :=
  let { sofar, pending } := s
  match next.push v with
  | .inl v => { sofar := sofar.push v, pending }
  | .inr next => { sofar, pending := pending.push next }

def pushOp (s : Gen term) (ctx : GenCtx term) (next : PartialTerm term) (op : Op Nat term) :=
  if op.args.isEmpty then
    s.push next (op.apply #[])
  else if op.args.size ≤ next.remTermSize ∧ next.termStack.size + 1 < ctx.maxDepth then
    { s with pending := s.pending.push (next.pushOp op) }
  else
    s

def add (s : Gen term) (val : term ⊕ PartialTerm term) : Gen term :=
  let { sofar, pending } := s
  match val with
  | .inl v => { sofar := sofar.push v, pending }
  | .inr p => { sofar, pending := pending.push p }

/-- Create state that will explore all terms in context -/
def addOpInstances (s : Gen term) (ctx : GenCtx term) (op : Op Nat term) : Gen term :=
  s.add (PartialTerm.init ctx.maxTermSize ctx.maxDepth op)

/-- Create state that will explore all terms in context -/
def init (ctx : GenCtx term) : Gen term :=
  ctx.topOps.foldl (init := {}) (·.addOpInstances ctx ·)

end Gen

/--
Generate terms until we reach the limit.
-/
partial
def generateTerms
    (ctx : GenCtx term)
    (s : Gen term)
    (limit : Nat := 0) :
    Array term × Gen term :=
  if limit > 0 ∧ s.sofar.size ≥ limit then
    (s.sofar, { s with sofar := #[] })
  else
    match s.pop with
    | none => (s.sofar, { s with sofar := #[] })
    | some (tp, next, s) =>
      let addVar (next : PartialTerm term) (i : Nat) (s : Gen term) : Gen term :=
            if next.usedVars[i]! = tp then
              match ctx.var tp i with
              | some v => s.push next v
              | none => s
            else
              s
      let s := next.usedVars.size.fold (init := s) (addVar next)
      let s :=
        let var := next.usedVars.size
        if var < ctx.maxVarCount then
          let next := { next with usedVars := next.usedVars.push tp }
          addVar next var s
        else
          s
      generateTerms ctx (ctx.ops[tp]!.foldl (init := s) (·.pushOp ctx next ·))

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

structure VarDecl (tp : Type) where
  idx : Nat
  ident : TSyntax `ident
  type : tp
  deriving Inhabited, Repr

instance : BEq (VarDecl tp) where
  beq x y := x.idx == y.idx

instance : Hashable (VarDecl tp) where
  hash v := hash v.idx

structure GenStats where
  maxTermSize : Nat := 9
  maxDepth : Nat := 3
  maxVarCount : Nat := 3

def mkCtx [BEq tp] [Hashable tp]
    (types : Array tp)
    (ops : List (Op tp val))
    (varGen : List (tp × CoreM Command))
    (mkVar : VarDecl tp → val)
    (stats : GenStats)
    (topOps : List (Op tp val) := ops) : CommandElabM (GenCtx val) := do
  let typeMap : HashMap tp Nat := Nat.fold (n := types.size) (init := {}) fun i s =>
        if p : i < types.size then
          s.insert types[i] i
        else
          s
  let typeFn (t : tp) := typeMap.findD t 0
  let addOp (a : Array (Array (Op Nat val))) (op : Op tp val) :=
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
    let addVars (p : LocalContext × LocalInstances × Array (Array val))
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
  pure { ops, topOps, maxTermSize, maxDepth, maxVarCount, lctx, linst, vars }

def runTests [BEq tp] [HasType val tp] [Value val] (stx : Syntax) (simp : val → val)(tac : Syntax.Tactic) (terms : Array val)
      : TermElabM Unit := do
  for tm in terms do
    if ← IO.checkCanceled then
      -- should never be visible to users!
      throw <| Exception.error .missing "Testing interrupted"
    let res := simp tm
    let t ← Value.render tm
    if HasType.typeOf tm != HasType.typeOf res then
      throwErrorAt stx m!"simp spec for {t} did not preserve type."
    withoutModifyingEnv $ do
      let exp ← Value.render res
      let u ← Lean.Elab.Term.elabTerm t none
      let type ← inferType u
      let checkGoalType ← mkCheckGoalType u type
      let expTerm ← Lean.Elab.Term.elabTerm exp (some type)
      let mvar ← mkFreshExprMVar (.some checkGoalType)
      let (goals, _) ← Lean.Elab.runTactic mvar.mvarId! tac.raw
      match goals with
      | [next] => do
        let (val, _, _) ← matchCheckGoalType stx (←next.getType)
        if !(← Meta.withReducible <| isDefEq val expTerm) then
          logErrorAt stx
            m!"{indentExpr u} reduces to{indentExpr val}\nbut is expected to reduce to {indentExpr expTerm}"
      | [] =>
        logErrorAt stx
          m!"{tac} closed goal, but is expected to reduce to {indentExpr expTerm}."
      | _ => do
        logErrorAt stx
          m!"{tac} produced multiple goals, but is expected to reduce to {indentExpr expTerm}."

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

partial
def runGen [BEq tp] [Hashable tp] [HasType term tp] [Value term]

      (stx : Syntax) (simp : term → term)
      (varGen : List (tp × CoreM Command))
      (mkVar : VarDecl tp → term)
      (stats : GenStats)
      (types : Array tp)
      (ops : List (Op tp term))
      (tac : Syntax.Tactic)
      (topOps : List (Op tp term) := ops)
      (concurrent : Bool := true) : CommandElabM Unit := do

  let ctx ← mkCtx (types := types) (ops := ops) (topOps := topOps) (varGen := varGen) (mkVar := mkVar) (stats := stats)

  let lctx := ctx.lctx
  let linst := ctx.linst

  let cmdCtx : Command.Context ← read
  let s ← get
  let ngen := s.ngen
  let env := s.env
  let maxRecDepth := s.maxRecDepth
  let heartbeats ← IO.getNumHeartbeats
  let options ← getOptions
  let cctx := mkCoreContext cmdCtx options maxRecDepth heartbeats
  let cstate : Core.State := { env := env, ngen := ngen, infoState.enabled := false }
  let mctx : Meta.Context := { lctx := lctx, localInstances := linst }
  let gen := Gen.init ctx
  if concurrent then
    let limit := 400
    let rec loop (gen : Gen term) (tasks : Array (Task (Except Exception MessageLog))) := do
      if gen.isEmpty then
        return tasks
      else
        IO.println s!"Writing task"
        let (terms, gen) := generateTerms ctx gen (limit := limit)
        let t ← runTests stx simp tac terms |> runTermElabM cctx cstate mctx |>.asTask
        loop gen (tasks.push t)
    let tasks ←
      profileitM Exception "simptest.launch" ({} : Options) (decl := .anonymous) do
        loop gen #[]

    profileitM Exception "simptest.execute" {} do
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
      let (terms, _) := generateTerms ctx gen
      runTests stx simp tac terms
    match r with
    | .error e => throw e
    | .ok m => modify fun s => { s with messages := s.messages ++ m }

/-

This file runs many tests on simp and other operations on Boolean/Prop
values.

It is intended to systematically evaluate simp strategies on different
operators.

Note. These tests use the simp tactic not necessarily because simp is
the best strategy for these particular examples, but rather simp may
wind up needing to discharge conditions during rewriting, and we need
tests showing that is has generally effective and predictable --
behavior.

General goals for simp are that the normal forms are sensible to a wide
range of users and that it performs well.  We also strive for Mathlib
compatibility.
-/

inductive BoolType where
  | prop
  | bool
  deriving BEq, DecidableEq, Hashable, Inhabited, Repr

inductive EqOp where
  | eqProp
  | eqBool
  | iffProp
  | beqBool
  deriving BEq, Repr

def EqOp.argType (op : EqOp) : BoolType :=
  match op with
  | .eqProp  | .iffProp => .prop
  | .beqBool | .eqBool => .bool

def EqOp.resultType (op : EqOp) : BoolType :=
  match op with
  | .eqProp | .eqBool | .iffProp => .prop
  | .beqBool => .bool

inductive NeOp where
  | neProp
  | neBool
  | bneBool
  deriving BEq, Repr

def NeOp.argType (op : NeOp) : BoolType :=
  match op with
  | .neProp  => .prop
  | .neBool | .bneBool => .bool

def NeOp.resultType (op : NeOp) : BoolType :=
  match op with
  | .neProp | .neBool  => .prop
  | .bneBool => .bool

inductive IteOp where
  | iteProp
  | iteBool
  | diteProp
  | diteBool
  | condBool
  deriving BEq, Repr

def IteOp.condType (op : IteOp) : BoolType :=
  match op with
  | .iteProp | .diteProp | .iteBool | .diteBool => .prop
  | .condBool => .bool

def IteOp.resultType (op : IteOp) : BoolType :=
  match op with
  | .iteProp | .diteProp => .prop
  | .iteBool | .diteBool | .condBool => .bool

/--
A first order term representing a `Bool` or `Prop` Lean expression
constructed from the operators described in the module header.

This groups operations that perform the same semantic function into the
same constructor while providing an operator type that identifies the
particular form of it.
-/
inductive BoolVal where
  | trueVal (tp : BoolType)
  | falseVal (tp : BoolType)
  | var (d : VarDecl BoolType)
    /--
    `(t : Prop)` when `t` is a `Bool`.

    Equivalent to `t = true`.
    -/
  | boolToProp (t : BoolVal)
    /-- `decide t` is the same as `p : Bool` -/
  | decide (t : BoolVal)
  | not (x   : BoolVal) (tp : BoolType)
  | and (x y : BoolVal) (tp : BoolType)
  | or  (x y : BoolVal) (tp : BoolType)
  | implies (x y : BoolVal)
  | eq (x y : BoolVal) (op : EqOp)
  | ne (x y : BoolVal) (op : NeOp)
  | ite (c t f : BoolVal) (op : IteOp)
  deriving BEq, Inhabited, Repr

namespace BoolVal

def typeOf (v : BoolVal) : BoolType :=
  match v with
  | .trueVal tp => tp
  | .falseVal tp => tp
  | .var d => d.type
  | .decide _ => .bool
  | .boolToProp _ => .prop
  | .not _ tp => tp
  | .and _ _ tp => tp
  | .or  _ _ tp => tp
  | .implies _ _ => .prop
  | .eq _ _ op => op.resultType
  | .ne _ _ op => op.resultType
  | .ite _ _ _ op => op.resultType

def render [Monad M] [MonadQuotation M] (v : BoolVal) : M Term :=
  match v with
  | .var d => do pure d.ident
  | .trueVal .bool  => `(true)
  | .trueVal .prop  => `(True)
  | .falseVal .bool => `(false)
  | .falseVal .prop => `(False)
  | .boolToProp t => do `(term| ($(←t.render) : Prop))
  | .decide t => do `(term| ($(←t.render) : Bool))
  | .not x .bool => do `(term| !$(←x.render))
  | .not x .prop => do `(term| ¬$(←x.render))
  | .and x y .bool => do `(term| $(←x.render) && $(←y.render))
  | .and x y .prop => do `(term| $(←x.render) ∧  $(←y.render))
  | .or  x y .bool => do `(term| $(←x.render) || $(←y.render))
  | .or  x y .prop => do `(term| $(←x.render) ∨  $(←y.render))
  | .implies x y => do `(term| $(←x.render) → $(←y.render))
  | .eq x y .eqProp | .eq x y .eqBool => do `(term| $(←x.render) = $(←y.render))
  | .eq x y .iffProp => do `(term| $(←x.render) ↔ $(←y.render))
  | .eq x y .beqBool => do `(term| $(←x.render) == $(←y.render))
  | .ne x y .neProp | .ne x y .neBool => do `(term| $(←x.render) ≠ $(←y.render))
  | .ne x y .bneBool => do `(term| $(←x.render) != $(←y.render))
  | .ite c t f op =>
    match op with
    | .iteProp | .iteBool => do
    `(term| if $(←c.render) then $(←t.render) else $(←f.render))
    | .diteProp | .diteBool => do
    `(term| if h : $(←c.render) then $(←t.render) else $(←f.render))
    | .condBool => do
      `(term| bif $(←c.render) then $(←t.render) else $(←f.render))

def map (f : BoolVal -> BoolVal) (v : BoolVal) : BoolVal :=
  match v with
  | .trueVal _ | .falseVal _ | .var _ => v
  | .boolToProp t => .boolToProp (f t)
  | .decide t => .decide (f t)
  | .not x tp   => .not (f x) tp
  | .and x y tp   => .and (f x) (f y) tp
  | .or  x y tp   => .or  (f x) (f y) tp
  | .implies x y => .implies (f x) (f y)
  | .eq x y op => .eq (f x) (f y) op
  | .ne x y op => .ne (f x) (f y) op
  | .ite c x y op => .ite (f c) (f x) (f y) op


def trueProp  : BoolVal := .trueVal .prop
def falseProp : BoolVal := .falseVal .prop
def trueBool  : BoolVal := .trueVal .bool
def falseBool : BoolVal := .falseVal .bool

local prefix:75 "~ " => fun t => BoolVal.not t (BoolVal.typeOf t)
local infix:40 "=v " => fun (x y : BoolVal) =>
  BoolVal.eq x y (match BoolVal.typeOf x with
            | .prop => EqOp.eqProp
            | .bool => EqOp.eqBool)
instance : AndOp BoolVal where
  and x y := BoolVal.and x y (BoolVal.typeOf x)
instance : OrOp BoolVal where
  or x y  := BoolVal.or x y (BoolVal.typeOf x)

section

@[match_pattern]
def iff (x y : BoolVal) : BoolVal := .eq x y .iffProp

@[match_pattern]
def eq_true (x : BoolVal) : BoolVal := .eq x (.trueVal .bool) .eqBool

@[match_pattern]
def eq_false (x : BoolVal) : BoolVal := .eq x (.falseVal .bool) .eqBool

def toBool (v : BoolVal) : BoolVal :=
  match v.typeOf with
  | .prop => .decide v
  | .bool => v

def toProp (v : BoolVal) : BoolVal :=
  match v.typeOf with
  | .prop => v
  | .bool => eq_true v

def coerceType (v : BoolVal) (type : BoolType) : BoolVal :=
  match v.typeOf, type with
  | .prop, .bool => .decide v
  | .bool, .prop => eq_true v
  | _, _ => v


/--
Returns true if we should consider `x` a complement of `y`.

Symmetric so also holds if `y` is a complement of `x`.
-/
def isComplement (x y : BoolVal) : Bool :=
  match x, y with
  | .not x _, y => x == y
  | x, .not y _ => x == y
  | .eq a b _, .ne c d _ => a.typeOf == c.typeOf && a == b && c == d
  | .ne a b _, .eq c d _ => a.typeOf == c.typeOf && a == b && c == d
  | eq_true x, eq_false y => x == y
  | eq_false x, eq_true y => x == y
  | _, _ => false


def resolveEq (thunks : List (term → term → Option term)) (x y : term) : Option term :=
  match thunks with
  | [] => none
  | fn :: thunks =>
    match fn x y with
    | none => resolveEq thunks x y
    | some r => some r

/--
Returns true if we should consider `x` a complement of `y`.

Symmetric so also holds if `y` is a complement of `x`.
-/
def isOrComplement (x y : BoolVal) (tp : BoolType) : Bool :=
  match x, y, tp with
  | .not x _, y, .bool => x == y
  | x, .not y _, .bool => x == y
  | .eq a b _, .ne c d _, _ => a.typeOf == c.typeOf && a == b && c == d
  | .ne a b _, .eq c d _, _ => a.typeOf == c.typeOf && a == b && c == d
  | eq_true x, eq_false y, _ => x == y
  | eq_false x, eq_true y, _ => x == y
  | _, _, _ => false

partial def simp (v : BoolVal) : BoolVal :=
  let v := map simp v
  match v with
  | .boolToProp b => simp <| eq_true b
  | .decide p =>
      match p with
      | .trueVal  _ => .trueVal  .bool
      | .falseVal _ => .falseVal .bool
      | .var _ => v
      | .boolToProp _ => panic! "Expected boolToProp to simplify away"
      | .not x _   => simp <| ~(.decide x)
      | .and x y _ => simp <| (.decide x) &&& (.decide y)
      | .or x y _  => simp <| (.decide x) ||| (.decide y)
      | .implies p q => simp <| ~(.decide p) ||| (.decide q)
      | .eq x y .eqBool =>
        match y with
        | .trueVal _ => x
        | .falseVal _ => simp (~ x)
        | _ => v
      | .eq x y .eqProp | iff x y =>
        simp <| .eq (.decide x) (.decide y) .beqBool
      | .ne _ _ op =>
        match op with
        | .neProp | .neBool => panic! "Expected ne to be reduced to not eq"
        | .bneBool => panic! "Unexpected bool"
      | .ite c t f op =>
        match op with
        | .iteProp => simp <| .ite c (.decide t) (.decide f) .iteBool
        | _ => v
      | .decide _ | .eq _ _ _ =>
        panic! s!"Unexpected prop {repr p} when bool expected."
  | .not t _ =>
    match t with
    | .trueVal tp => .falseVal tp
    | .falseVal tp => .trueVal tp
    | .not t _ => t
    | .and x y .prop => simp <| .implies x (.not y .prop)
    | .and x y .bool => simp <| .or (.not x .bool) (.not y .bool) .bool
    | .or x y  tp    => simp <| .and (.not x tp) (.not y tp) tp
    | .implies x y => simp <| .and x (.not y .prop) .prop
    | .eq b (.trueVal  .bool) .eqBool => .eq b (.falseVal .bool) .eqBool
    | .eq b (.falseVal .bool) .eqBool => .eq b (.trueVal  .bool) .eqBool
    | .eq b (.not c .bool) .eqBool => simp <| .eq b c .eqBool
    | .eq (.not b .bool) c .eqBool => simp <| .eq b c .eqBool
    | .ne b c .neBool  => .eq b c .eqBool
    | .ite c t f .iteProp =>
        match t, f with
        | eq_true  t, eq_true  f => .ite c (eq_false t) (eq_false f) .iteProp
        | eq_true  t, eq_false f => .ite c (eq_false t) (eq_true  f) .iteProp
        | eq_false t, eq_true  f => .ite c (eq_true t)  (eq_false f) .iteProp
        | eq_false t, eq_false f => .ite c (eq_true t)  (eq_true  f) .iteProp
        | _, _ => v
    | _ => v
  | .and x y tp => Id.run do
      if let .trueVal _ := x then
        return y
      if let .falseVal _ := x then
        return x
      if let .trueVal _ := y then
        return x
      if let .falseVal _ := y then
        return y
      if let .and _xl xr _ := x then
        if xr == y then return x
      if let .and yl _yr _ := y then
        if x == yl then return y
      if x == y then
        return x
      else if isComplement x y then
        return .falseVal tp
      else
        return v
  | .or x y tp => Id.run do
      -- Hardcoded for and-or-imp special case
      if let .and x1 x2 .prop := x then
        if let .implies y1 y2 := y then
          if x1 == y1 then
            return (simp <| .implies x1 (.or x2 y2 .prop))
      if let .falseVal _ := x then
        return y
      if let .trueVal _ := x then
        return x
      if let .falseVal _ := y then
        return x
      if let .trueVal _ := y then
        return y
      if let .or _xl xr _ := x then
        if xr == y then return x
      if let .or yl _yr _ := y then
        if x == yl then return y
      if x == y then
        return x
      if isOrComplement x y tp then
          return .trueVal tp
      pure v
  | .implies x y =>
    match x, y with
    | .trueVal _, y => y
    | .falseVal _, _ => .trueVal .prop
    | _, .trueVal _ => y
    | _, .falseVal _ => simp <| .not x .prop
    | .and a b _, y => simp <| .implies a (.implies b y)
    | x, y => Id.run <| do
      if x == y then
        return (.trueVal .prop)
      if let eq_true b := x then
        if let eq_false c := y then
          if b == c then
            return y
      if let eq_false b := x then
        if let eq_true c := y then
          if b == c then
            return y
      if let .not x _ := x then
        if x == y then
          return x
      if let .not yn _ := y then
        if x == yn then
          return y

      return v
  | .eq (.trueVal _) y op =>
    match y with
    | .falseVal _ => .falseVal op.resultType
    | .trueVal _ => .trueVal op.resultType
    | _ =>
      match op with
      | .eqBool => simp <| .eq y (.trueVal .bool) .eqBool
      | .eqProp | .iffProp | .beqBool => y
  | .eq (.falseVal tp) y op =>
    match y with
    | .trueVal  _ => .falseVal op.resultType
    | .falseVal _ => .trueVal  op.resultType
    | _ =>
      match op with
      | .eqBool =>
        simp <| eq_false y
      | _ =>
        simp <| .not y tp
  | .eq x (.trueVal .bool) .eqBool =>
    (match x with
    | .trueVal _ | .falseVal _ | .implies _ _ | .boolToProp _ =>
      panic! "Unexpected term."
    | .var _ => v
    | .decide t => t
    | .not x _   => simp <| eq_false x
    | .and x y _  => simp <| eq_true x &&& eq_true y
    | .or x y _   => simp <| eq_true x ||| eq_true y
    | .eq x y .beqBool => simp <| .eq x y .eqBool
    | .ne x y .bneBool => simp <| .ne x y .neBool
    | .ite c t f op =>
      (match op with
      | .iteBool | .condBool =>
        simp <| .ite (coerceType c .prop) (eq_true t) (eq_true f) .iteProp
      | .diteBool => panic! "expected dite to simplify away."
      | _ => panic! "Unexpected prop when bool expected.")
    | .eq _ _ _ | .ne _ _ _ =>
        panic! "Unexpected prop when bool expected.")
  | .eq x (.trueVal _) _op => x
  | .eq x (.falseVal _) .eqBool  =>
    match x with
    | .trueVal _ | .falseVal _ | .implies _ _ | .boolToProp _ =>
      panic! "Unexpected term."
    | .var _ => v
    | .decide t =>
      simp <| .not t .prop
    | .not x _   =>
      simp <| .eq x (.trueVal .bool) .eqBool
    | .and x y _ => simp <| .implies (eq_true x) (eq_false y)
    | .or  x y _ => simp <| .and (eq_false x) (eq_false y) .prop
    | .eq x y .beqBool => simp <| .not (.eq x y .eqBool) .prop
    | .ne x y .bneBool => simp <| .eq x y .eqBool
    | .ite c t f _ =>
      simp <| .ite (coerceType c .prop) (eq_false t) (eq_false f) .iteProp
    | .eq _ _ _ | .ne _ _ _ =>
        panic! "Unexpected prop when bool expected."
   -- N.B. bool ops other than .eqBool do not change type.
  | .eq x y op => Id.run do
    if let .falseVal tp := y then
      return simp (.not x tp)
    if x == y then
      return (.trueVal op.resultType)
    if isComplement x y then
      return (.falseVal op.resultType)
    if let .beqBool := op then
      if let .eq x1 x2 .beqBool := x then
        if x2 == y then
          return x1
      if let .eq y1 y2 .beqBool := y then
        if x == y1 then
          return y2
    match op with
    | .eqProp | .iffProp | .eqBool =>
      let checks : List (BoolVal → BoolVal → Option BoolVal) := [
        fun x y =>
          if let .and x1 x2 _ := x then
            if x1 == y then
              some <| .implies (toProp y) (toProp x2)
            else if x2 == y then
              some <| .implies (toProp y) (toProp x1)
            else none
          else none,
        fun x y =>
          if let .and y1 y2 _ := y then
            if x == y1 then
              some <| .implies (toProp x) (toProp y2)
            else if x == y2 then
              some <| .implies (toProp x) (toProp y1)
            else none
          else none,
        fun x y =>
          if let .or x1 x2 _ := x then
            if x1 == y then
              some <| .implies (toProp x2) (toProp y)
            else if x2 == y then
              some <| .implies (toProp x1) (toProp y)
            else none
          else none,
        fun x y =>
          if let .or y1 y2 _ := y then
            if x == y1 then
              some <| .implies (toProp y2) (toProp x)
            else if x == y2 then
              some <| .implies (toProp y1) (toProp x)
            else none
          else none,
        fun x y =>
          if let .or x1 x2 _ := x then
            if x1 == y then
              some <| .implies (toProp x2) (toProp y)
            else if x2 == y then
              some <| .implies (toProp x1) (toProp y)
            else none
          else none,
        fun x y =>
          if let .implies x1 x2 := x then
            if x2 == y then
              pure <| .or x1 y .prop
            else none
          else none,
        fun x y =>
          if let .implies y1 y2 := y then
            if x == y2 then
              pure <| .or y1 x .prop
            else none
          else none
      ]
      match resolveEq checks x y with
      | some r => return (simp r)
      | none => pure ()
    | _ =>
      pure ()
    match op with
    | .eqProp | .iffProp =>
      match x, y with
      -- The cases below simplify the bool to prop normal forms (b = true, b = false) while
      -- avoiding distributing not over the normal form.
      | eq_true  x, eq_true  y => simp <| .eq x y .eqBool
      | eq_false x, eq_false y => simp <| .eq (~ x) (~ y) .eqBool
      | eq_true  x, eq_false y => simp <| .eq x (~ y) .eqBool
      | eq_false x, eq_true  y => simp <| .eq (~ x) y .eqBool
      | _, _ => iff x y
    | .eqBool =>
      match x, y with
      | .decide x, .decide y => iff x y
      | _, _ => v
    | .beqBool => v
  | .ne x y op => Id.run do
    if let .neBool := op then
      return simp (.not (.eq x y .eqBool) .prop)
    if let .neProp := op then
      return simp (.not (.eq x y .eqProp) .prop)
    if let .trueVal _ := x then
      return simp (~y)
    if let .falseVal _ := x then
      return y
    if let .trueVal _ := y then
      return simp (~x)
    if let .falseVal _ := y then
      return x
    if x == y then
      return .falseVal .bool
    if isComplement x y then
      return .trueVal .bool
    if let .ne y1 y2 .bneBool := y then
      if x == y1 then
        return y2
    pure <|
      match x, y with
      | .ne a b .bneBool, c => simp <| .ne a (.ne b c .bneBool) .bneBool
      | .not x _, .not y _ =>  simp <| .ne x y .bneBool
      | _, _ => v
  | .ite c t f op => Id.run do
    if let .trueVal _ := c then
      return t
    if let .falseVal _ := c then
      return f
    if let .not c _ := c then
      return simp <| .ite c f t op
    if let .falseVal tp := t then
      return simp <| (~(coerceType c tp)) &&& f
    if let .falseVal tp := f then
      return simp <| (coerceType c tp) &&& t
    -- NB. The patterns where a branch is true are
    -- intentionally after branches with a
    -- false because we prefer to introduce conjunction
    -- over disjunction/implies when overlapping.
    if let .trueVal _ := t then
      let r :=
        match op with
        | .iteBool => simp <| toBool c ||| f
        | .iteProp => simp <| .implies (~c) f
        | .condBool => simp <|  c ||| f
        | _ => v
      return r
    if let .trueVal _ := f then
      let r :=
        match op with
        | .iteBool  => simp <| ~(toBool c) ||| t
        | .iteProp  => simp <| .implies c t
        | .condBool => simp <| ~c ||| t
        | _ => v
      return r
    if t == f then
      return t
    let matchProp c x :=
          match op with
          | .iteBool =>
              if let .decide x := x then
                if c == x then
                  some (toBool c)
                else
                  none
              else
                none
          | .iteProp | .condBool => if c == x then some c else none
          | _ => none
    if let some c := matchProp c t then
      let r :=
        match f.typeOf with
        | .bool => simp <| c ||| f
        | .prop => simp <| .implies (.not c .prop) f
      return r
    if let some c := matchProp c f then
      return simp <| c &&& t
    let op := match op with
              | .diteProp => .iteProp
              | .diteBool => .iteBool
              | _ => op
    .ite c t f op
  | .trueVal _ | .falseVal _ | .var _ => v
end
set_option profiler false

end BoolVal

instance : HasType BoolVal BoolType where
  typeOf val := val.typeOf

instance : Value BoolVal where
  render val := val.render

section
open BoolVal BoolType

def trueOp  (tp : BoolType) := mkOp [] tp fun _ => trueVal  tp
def falseOp (tp : BoolType) := mkOp [] tp fun _ => falseVal tp
def boolToPropOp := mkOp [.bool] prop fun a => boolToProp (a[0]!)
def propToBoolOp := mkOp [prop] bool fun a => BoolVal.decide (a[0]!)

def notOp (tp : BoolType) := mkOp [tp] tp fun a => not (a[0]!) tp
def andOp (tp : BoolType) := mkOp [tp, tp] tp fun a => and (a[0]!) (a[1]!) tp
def orOp  (tp : BoolType) := mkOp [tp, tp] tp fun a => or  (a[0]!) (a[1]!) tp
def impliesOp := mkOp [.prop, .prop] prop fun a => implies  (a[0]!) (a[1]!)
def eqOp  (op : EqOp)  :=
  mkOp [op.argType, op.argType] op.resultType fun a => eq (a[0]!) (a[1]!) op
def neOp  (op : NeOp)  :=
  mkOp [op.argType, op.argType] op.resultType fun a => ne (a[0]!) (a[1]!) op
def iteOp (op : IteOp) :=
  let rtp := op.resultType
  mkOp [op.condType, rtp, rtp] rtp fun a => ite (a[0]!) (a[1]!) (a[2]!) op

end

def mkBoolDecl : CoreM Command := `(variable (b : Bool))
def mkDecidablePropDecl : CoreM Command := `(variable (p : Prop) [Decidable p])

syntax:lead (name := boolTestElab) "#boolTest" : command

@[command_elab boolTestElab]
def elabGenTest : CommandElab := fun stx => do
  let baseOps := [
      trueOp  .bool,  trueOp .prop,
      falseOp .bool, falseOp .prop,
      boolToPropOp, propToBoolOp,
      notOp .bool, notOp .prop,
      andOp .bool, andOp .prop,
      orOp .bool,  orOp .prop,
      impliesOp
  ]
  let eqOps := [ eqOp .eqProp, eqOp .eqBool, eqOp .iffProp, eqOp .beqBool ]
  let neOps := [ neOp .neProp, neOp .neBool, neOp .bneBool ]
  let iteOps := [
    iteOp .iteProp, iteOp .iteBool,
    --iteOp .diteProp,  iteOp .diteBool,
    iteOp .condBool
  ]
  let types := #[.prop, .bool]
  let ops := baseOps ++ eqOps ++ neOps ++ iteOps
  let varGen : List (BoolType × CoreM Command) := [
      (.bool, mkBoolDecl),
      (.prop, mkDecidablePropDecl)
  ]
  let stats : GenStats := { maxTermSize := 7, maxDepth := 3, maxVarCount := 2 }
  let tac : Syntax.Tactic ← `(tactic|try simp)
  runGen stx BoolVal.simp varGen BoolVal.var stats types ops (topOps := ops) tac

set_option maxHeartbeats 10000000
#boolTest
