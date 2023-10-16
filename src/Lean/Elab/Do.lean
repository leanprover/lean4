/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Term
import Lean.Elab.BindersUtil
import Lean.Elab.PatternVar
import Lean.Elab.Quotation.Util
import Lean.Parser.Do

-- HACK: avoid code explosion until heuristics are improved
set_option compiler.reuse false

namespace Lean.Elab.Term
open Lean.Parser.Term
open Meta
open TSyntax.Compat

private def getDoSeqElems (doSeq : Syntax) : List Syntax :=
  if doSeq.getKind == ``Parser.Term.doSeqBracketed then
    doSeq[1].getArgs.toList.map fun arg => arg[0]
  else if doSeq.getKind == ``Parser.Term.doSeqIndent then
    doSeq[0].getArgs.toList.map fun arg => arg[0]
  else
    []

private def getDoSeq (doStx : Syntax) : Syntax :=
  doStx[1]

@[builtin_term_elab liftMethod] def elabLiftMethod : TermElab := fun stx _ =>
  throwErrorAt stx "invalid use of `(<- ...)`, must be nested inside a 'do' expression"

/-- Return true if we should not lift `(<- ...)` actions nested in the syntax nodes with the given kind. -/
private def liftMethodDelimiter (k : SyntaxNodeKind) : Bool :=
  k == ``Parser.Term.do ||
  k == ``Parser.Term.doSeqIndent ||
  k == ``Parser.Term.doSeqBracketed ||
  k == ``Parser.Term.termReturn ||
  k == ``Parser.Term.termUnless ||
  k == ``Parser.Term.termTry ||
  k == ``Parser.Term.termFor

/-- Given `stx` which is a `letPatDecl`, `letEqnsDecl`, or `letIdDecl`, return true if it has binders. -/
private def letDeclArgHasBinders (letDeclArg : Syntax) : Bool :=
  let k := letDeclArg.getKind
  if k == ``Parser.Term.letPatDecl then
    false
  else if k == ``Parser.Term.letEqnsDecl then
    true
  else if k == ``Parser.Term.letIdDecl then
    -- letIdLhs := binderIdent >> checkWsBefore "expected space before binders" >> many (ppSpace >> letIdBinder)) >> optType
    let binders := letDeclArg[1]
    binders.getNumArgs > 0
  else
    false

/-- Return `true` if the given `letDecl` contains binders. -/
private def letDeclHasBinders (letDecl : Syntax) : Bool :=
  letDeclArgHasBinders letDecl[0]

/-- Return true if we should generate an error message when lifting a method over this kind of syntax. -/
private def liftMethodForbiddenBinder (stx : Syntax) : Bool :=
  let k := stx.getKind
  if k == ``Parser.Term.fun || k == ``Parser.Term.matchAlts ||
     k == ``Parser.Term.doLetRec || k == ``Parser.Term.letrec  then
     -- It is never ok to lift over this kind of binder
    true
  -- The following kinds of `let`-expressions require extra checks to decide whether they contain binders or not
  else if k == ``Parser.Term.let then
    letDeclHasBinders stx[1]
  else if k == ``Parser.Term.doLet then
    letDeclHasBinders stx[2]
  else if k == ``Parser.Term.doLetArrow then
    letDeclArgHasBinders stx[2]
  else
    false

private partial def hasLiftMethod : Syntax → Bool
  | Syntax.node _ k args =>
    if liftMethodDelimiter k then false
    -- NOTE: We don't check for lifts in quotations here, which doesn't break anything but merely makes this rare case a
    -- bit slower
    else if k == ``Parser.Term.liftMethod then true
    else args.any hasLiftMethod
  | _ => false

structure ExtractMonadResult where
  m            : Expr
  returnType   : Expr
  expectedType : Expr

private def mkUnknownMonadResult : MetaM ExtractMonadResult := do
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  let m ← mkFreshExprMVar (← mkArrow (mkSort (mkLevelSucc u)) (mkSort (mkLevelSucc v)))
  let returnType ← mkFreshExprMVar (mkSort (mkLevelSucc u))
  return { m, returnType, expectedType := mkApp m returnType }

private partial def extractBind (expectedType? : Option Expr) : TermElabM ExtractMonadResult := do
  let some expectedType := expectedType? | mkUnknownMonadResult
  let extractStep? (type : Expr) : MetaM (Option ExtractMonadResult) := do
    let .app m returnType := type | return none
    try
      let bindInstType ← mkAppM ``Bind #[m]
      discard <| Meta.synthInstance bindInstType
      return some { m, returnType, expectedType }
    catch _ =>
      return none
  let rec extract? (type : Expr) : MetaM (Option ExtractMonadResult) := do
    match (← extractStep? type) with
    | some r => return r
    | none =>
      let typeNew ← whnfCore type
      if typeNew != type then
        extract? typeNew
      else
        if typeNew.getAppFn.isMVar then
          mkUnknownMonadResult
        else match (← unfoldDefinition? typeNew) with
          | some typeNew => extract? typeNew
          | none => return none
  match (← extract? expectedType) with
  | some r => return r
  | none   => throwError "invalid `do` notation, expected type is not a monad application{indentExpr expectedType}\nYou can use the `do` notation in pure code by writing `Id.run do` instead of `do`, where `Id` is the identity monad."

namespace Do

abbrev Var := Syntax  -- TODO: should be `Ident`

/-- A `doMatch` alternative. `vars` is the array of variables declared by `patterns`. -/
structure Alt (σ : Type) where
  ref : Syntax
  vars : Array Var
  patterns : Syntax
  rhs : σ
  deriving Inhabited

/--
  Auxiliary datastructure for representing a `do` code block, and compiling "reassignments" (e.g., `x := x + 1`).
  We convert `Code` into a `Syntax` term representing the:
  - `do`-block, or
  - the visitor argument for the `forIn` combinator.

  We say the following constructors are terminals:
  - `break`:    for interrupting a `for x in s`
  - `continue`: for interrupting the current iteration of a `for x in s`
  - `return e`: for returning `e` as the result for the whole `do` computation block
  - `action a`: for executing action `a` as a terminal
  - `ite`:      if-then-else
  - `match`:    pattern matching
  - `jmp`       a goto to a join-point

  We say the terminals `break`, `continue`, `action`, and `return` are "exit points"

  Note that, `return e` is not equivalent to `action (pure e)`. Here is an example:
  ```
  def f (x : Nat) : IO Unit := do
  if x == 0 then
     return ()
  IO.println "hello"
  ```
  Executing `#eval f 0` will not print "hello". Now, consider
  ```
  def g (x : Nat) : IO Unit := do
  if x == 0 then
     pure ()
  IO.println "hello"
  ```
  The `if` statement is essentially a noop, and "hello" is printed when we execute `g 0`.

  - `decl` represents all declaration-like `doElem`s (e.g., `let`, `have`, `let rec`).
    The field `stx` is the actual `doElem`,
    `vars` is the array of variables declared by it, and `cont` is the next instruction in the `do` code block.
    `vars` is an array since we have declarations such as `let (a, b) := s`.

  - `reassign` is an reassignment-like `doElem` (e.g., `x := x + 1`).

  - `joinpoint` is a join point declaration: an auxiliary `let`-declaration used to represent the control-flow.

  - `seq a k` executes action `a`, ignores its result, and then executes `k`.
    We also store the do-elements `dbg_trace` and `assert!` as actions in a `seq`.

  A code block `C` is well-formed if
  - For every `jmp ref j as` in `C`, there is a `joinpoint j ps b k` and `jmp ref j as` is in `k`, and
    `ps.size == as.size` -/
inductive Code where
  | decl         (xs : Array Var) (doElem : Syntax) (k : Code)
  | reassign     (xs : Array Var) (doElem : Syntax) (k : Code)
  /-- The Boolean value in `params` indicates whether we should use `(x : typeof! x)` when generating term Syntax or not -/
  | joinpoint    (name : Name) (params : Array (Var × Bool)) (body : Code) (k : Code)
  | seq          (action : Syntax) (k : Code)
  | action       (action : Syntax)
  | break        (ref : Syntax)
  | continue     (ref : Syntax)
  | return       (ref : Syntax) (val : Syntax)
  /-- Recall that an if-then-else may declare a variable using `optIdent` for the branches `thenBranch` and `elseBranch`. We store the variable name at `var?`. -/
  | ite          (ref : Syntax) (h? : Option Var) (optIdent : Syntax) (cond : Syntax) (thenBranch : Code) (elseBranch : Code)
  | match        (ref : Syntax) (gen : Syntax) (discrs : Syntax) (optMotive : Syntax) (alts : Array (Alt Code))
  | jmp          (ref : Syntax) (jpName : Name) (args : Array Syntax)
  deriving Inhabited

def Code.getRef? : Code → Option Syntax
  | .decl _ doElem _     => doElem
  | .reassign _ doElem _ => doElem
  | .joinpoint ..        => none
  | .seq a _             => a
  | .action a            => a
  | .break ref           => ref
  | .continue ref        => ref
  | .return ref _        => ref
  | .ite ref ..          => ref
  | .match ref ..        => ref
  | .jmp ref ..          => ref

abbrev VarSet := RBMap Name Syntax Name.cmp

/-- A code block, and the collection of variables updated by it. -/
structure CodeBlock where
  code  : Code
  uvars : VarSet := {} -- set of variables updated by `code`

private def varSetToArray (s : VarSet) : Array Var :=
  s.fold (fun xs _ x => xs.push x) #[]

private def varsToMessageData (vars : Array Var) : MessageData :=
  MessageData.joinSep (vars.toList.map fun n => MessageData.ofName (n.getId.simpMacroScopes)) " "

partial def CodeBlocl.toMessageData (codeBlock : CodeBlock) : MessageData :=
  let us := MessageData.ofList <| (varSetToArray codeBlock.uvars).toList.map MessageData.ofSyntax
  let rec loop : Code → MessageData
    | .decl xs _ k           => m!"let {varsToMessageData xs} := ...\n{loop k}"
    | .reassign xs _ k       => m!"{varsToMessageData xs} := ...\n{loop k}"
    | .joinpoint n ps body k => m!"let {n.simpMacroScopes} {varsToMessageData (ps.map Prod.fst)} := {indentD (loop body)}\n{loop k}"
    | .seq e k               => m!"{e}\n{loop k}"
    | .action e              => e
    | .ite _ _ _ c t e       => m!"if {c} then {indentD (loop t)}\nelse{loop e}"
    | .jmp _ j xs            => m!"jmp {j.simpMacroScopes} {xs.toList}"
    | .break _               => m!"break {us}"
    | .continue _            => m!"continue {us}"
    | .return _ v            => m!"return {v} {us}"
    | .match _ _ ds _ alts   =>
      m!"match {ds} with"
      ++ alts.foldl (init := m!"") fun acc alt => acc ++ m!"\n| {alt.patterns} => {loop alt.rhs}"
  loop codeBlock.code

/-- Return true if the give code contains an exit point that satisfies `p` -/
partial def hasExitPointPred (c : Code) (p : Code → Bool) : Bool :=
  let rec loop : Code → Bool
    | .decl _ _ k         => loop k
    | .reassign _ _ k     => loop k
    | .joinpoint _ _ b k  => loop b || loop k
    | .seq _ k            => loop k
    | .ite _ _ _ _ t e    => loop t || loop e
    | .match _ _ _ _ alts => alts.any (loop ·.rhs)
    | .jmp ..             => false
    | c                   => p c
  loop c

def hasExitPoint (c : Code) : Bool :=
  hasExitPointPred c fun _ => true

def hasReturn (c : Code) : Bool :=
  hasExitPointPred c fun
    | .return .. => true
    | _ => false

def hasTerminalAction (c : Code) : Bool :=
  hasExitPointPred c fun
    | .action _ => true
    | _ => false

def hasBreakContinue (c : Code) : Bool :=
  hasExitPointPred c fun
    | .break _    => true
    | .continue _ => true
    | _ => false

def hasBreakContinueReturn (c : Code) : Bool :=
  hasExitPointPred c fun
    | .break _    => true
    | .continue _ => true
    | .return _ _ => true
    | _ => false

def mkAuxDeclFor {m} [Monad m] [MonadQuotation m] (e : Syntax) (mkCont : Syntax → m Code) : m Code := withRef e <| withFreshMacroScope do
  let y ← `(y)
  let doElem ← `(doElem| let y ← $e:term)
  -- Add elaboration hint for producing sane error message
  let y ← `(ensure_expected_type% "type mismatch, result value" $y)
  let k ← mkCont y
  return .decl #[y] doElem k

/-- Convert `action _ e` instructions in `c` into `let y ← e; jmp _ jp (xs y)`. -/
partial def convertTerminalActionIntoJmp (code : Code) (jp : Name) (xs : Array Var) : MacroM Code :=
  let rec loop : Code → MacroM Code
    | .decl xs stx k         => return .decl xs stx (← loop k)
    | .reassign xs stx k     => return .reassign xs stx (← loop k)
    | .joinpoint n ps b k    => return .joinpoint n ps (← loop b) (← loop k)
    | .seq e k               => return .seq e (← loop k)
    | .ite ref x? h c t e    => return .ite ref x? h c (← loop t) (← loop e)
    | .match ref g ds t alts => return .match ref g ds t (← alts.mapM fun alt => do pure { alt with rhs := (← loop alt.rhs) })
    | .action e              => mkAuxDeclFor e fun y =>
      let ref := e
      -- We jump to `jp` with xs **and** y
      let jmpArgs := xs.push y
      return Code.jmp ref jp jmpArgs
    | c                            => return c
  loop code

structure JPDecl where
  name : Name
  params : Array (Var × Bool)
  body : Code

def attachJP (jpDecl : JPDecl) (k : Code) : Code :=
  Code.joinpoint jpDecl.name jpDecl.params jpDecl.body k

def attachJPs (jpDecls : Array JPDecl) (k : Code) : Code :=
  jpDecls.foldr attachJP k

def mkFreshJP (ps : Array (Var × Bool)) (body : Code) : TermElabM JPDecl := do
  let ps ← if ps.isEmpty then
    let y ← `(y)
    pure #[(y.raw, false)]
  else
    pure ps
  -- Remark: the compiler frontend implemented in C++ currently detects jointpoints created by
  -- the "do" notation by testing the name. See hack at method `visit_let` at `lcnf.cpp`
  -- We will remove this hack when we re-implement the compiler frontend in Lean.
  let name ← mkFreshUserName `__do_jp
  pure { name := name, params := ps, body := body }

def addFreshJP (ps : Array (Var × Bool)) (body : Code) : StateRefT (Array JPDecl) TermElabM Name := do
  let jp ← mkFreshJP ps body
  modify fun (jps : Array JPDecl) => jps.push jp
  pure jp.name

def insertVars (rs : VarSet) (xs : Array Var) : VarSet :=
  xs.foldl (fun rs x => rs.insert x.getId x) rs

def eraseVars (rs : VarSet) (xs : Array Var) : VarSet :=
  xs.foldl (·.erase ·.getId) rs

def eraseOptVar (rs : VarSet) (x? : Option Var) : VarSet :=
  match x? with
  | none   => rs
  | some x => rs.insert x.getId x

/-- Create a new jointpoint for `c`, and jump to it with the variables `rs` -/
def mkSimpleJmp (ref : Syntax) (rs : VarSet) (c : Code) : StateRefT (Array JPDecl) TermElabM Code := do
  let xs := varSetToArray rs
  let jp ← addFreshJP (xs.map fun x => (x, true)) c
  if xs.isEmpty then
    let unit ← ``(Unit.unit)
    return Code.jmp ref jp #[unit]
  else
    return Code.jmp ref jp xs

/-- Create a new joinpoint that takes `rs` and `val` as arguments. `val` must be syntax representing a pure value.
   The body of the joinpoint is created using `mkJPBody yFresh`, where `yFresh`
   is a fresh variable created by this method. -/
def mkJmp (ref : Syntax) (rs : VarSet) (val : Syntax) (mkJPBody : Syntax → MacroM Code) : StateRefT (Array JPDecl) TermElabM Code := do
  let xs := varSetToArray rs
  let args := xs.push val
  let yFresh ← withRef ref `(y)
  let ps := xs.map fun x => (x, true)
  let ps := ps.push (yFresh, false)
  let jpBody ← liftMacroM <| mkJPBody yFresh
  let jp ← addFreshJP ps jpBody
  return Code.jmp ref jp args

/-- `pullExitPointsAux rs c` auxiliary method for `pullExitPoints`, `rs` is the set of update variable in the current path.  -/
partial def pullExitPointsAux (rs : VarSet) (c : Code) : StateRefT (Array JPDecl) TermElabM Code :=
  match c with
  | .decl xs stx k         => return .decl xs stx (← pullExitPointsAux (eraseVars rs xs) k)
  | .reassign xs stx k     => return .reassign xs stx (← pullExitPointsAux (insertVars rs xs) k)
  | .joinpoint j ps b k    => return .joinpoint j ps (← pullExitPointsAux rs b) (← pullExitPointsAux rs k)
  | .seq e k               => return .seq e (← pullExitPointsAux rs k)
  | .ite ref x? o c t e    => return .ite ref x? o c (← pullExitPointsAux (eraseOptVar rs x?) t) (← pullExitPointsAux (eraseOptVar rs x?) e)
  | .match ref g ds t alts => return .match ref g ds t (← alts.mapM fun alt => do pure { alt with rhs := (← pullExitPointsAux (eraseVars rs alt.vars) alt.rhs) })
  | .jmp ..                => return  c
  | .break ref             => mkSimpleJmp ref rs (.break ref)
  | .continue ref          => mkSimpleJmp ref rs (.continue ref)
  | .return ref val        => mkJmp ref rs val (fun y => return .return ref y)
  | .action e              =>
    -- We use `mkAuxDeclFor` because `e` is not pure.
    mkAuxDeclFor e fun y =>
      let ref := e
      mkJmp ref rs y (fun yFresh => return .action (← ``(Pure.pure $yFresh)))

/--
Auxiliary operation for adding new variables to the collection of updated variables in a CodeBlock.
When a new variable is not already in the collection, but is shadowed by some declaration in `c`,
we create auxiliary join points to make sure we preserve the semantics of the code block.
Example: suppose we have the code block `print x; let x := 10; return x`. And we want to extend it
with the reassignment `x := x + 1`. We first use `pullExitPoints` to create
```
let jp (x!1) :=  return x!1;
print x;
let x := 10;
jmp jp x
```
and then we add the reassignment
```
x := x + 1
let jp (x!1) := return x!1;
print x;
let x := 10;
jmp jp x
```
Note that we created a fresh variable `x!1` to avoid accidental name capture.
As another example, consider
```
print x;
let x := 10
y := y + 1;
return x;
```
We transform it into
```
let jp (y x!1) := return x!1;
print x;
let x := 10
y := y + 1;
jmp jp y x
```
and then we add the reassignment as in the previous example.
We need to include `y` in the jump, because each exit point is implicitly returning the set of
update variables.

We implement the method as follows. Let `us` be `c.uvars`, then
1- for each `return _ y` in `c`, we create a join point
  `let j (us y!1) := return y!1`
   and replace the `return _ y` with `jmp us y`
2- for each `break`, we create a join point
  `let j (us) := break`
   and replace the `break` with `jmp us`.
3- Same as 2 for `continue`.
-/
def pullExitPoints (c : Code) : TermElabM Code := do
  if hasExitPoint c then
    let (c, jpDecls) ← (pullExitPointsAux {} c).run #[]
    return attachJPs jpDecls c
  else
    return c

partial def extendUpdatedVarsAux (c : Code) (ws : VarSet) : TermElabM Code :=
  let rec update (c : Code) : TermElabM Code := do
    match c with
    | .joinpoint j ps b k    => return .joinpoint j ps (← update b) (← update k)
    | .seq e k               => return .seq e (← update k)
    | .match ref g ds t alts =>
      if alts.any fun alt => alt.vars.any fun x => ws.contains x.getId then
        -- If a pattern variable is shadowing a variable in ws, we `pullExitPoints`
        pullExitPoints c
      else
        return .match ref g ds t (← alts.mapM fun alt => do pure { alt with rhs := (← update alt.rhs) })
    | .ite ref none o c t e => return .ite ref none o c (← update t) (← update e)
    | .ite ref (some h) o cond t e =>
      if ws.contains h.getId then
        -- if the `h` at `if h:c then t else e` shadows a variable in `ws`, we `pullExitPoints`
        pullExitPoints c
      else
        return Code.ite ref (some h) o cond (← update t) (← update e)
    | .reassign xs stx k => return .reassign xs stx (← update k)
    | .decl xs stx k => do
      if xs.any fun x => ws.contains x.getId then
        -- One the declared variables is shadowing a variable in `ws`
        pullExitPoints c
      else
        return .decl xs stx (← update k)
    | c => return  c
  update c

/--
Extend the set of updated variables. It assumes `ws` is a super set of `c.uvars`.
We **cannot** simply update the field `c.uvars`, because `c` may have shadowed some variable in `ws`.
See discussion at `pullExitPoints`.
-/
partial def extendUpdatedVars (c : CodeBlock) (ws : VarSet) : TermElabM CodeBlock := do
  if ws.any fun x _ => !c.uvars.contains x then
    -- `ws` contains a variable that is not in `c.uvars`, but in `c.dvars` (i.e., it has been shadowed)
    pure { code := (← extendUpdatedVarsAux c.code ws), uvars := ws }
  else
    pure { c with uvars := ws }

private def union (s₁ s₂ : VarSet) : VarSet :=
  s₁.fold (·.insert ·) s₂

/--
Given two code blocks `c₁` and `c₂`, make sure they have the same set of updated variables.
Let `ws` the union of the updated variables in `c₁‵ and ‵c₂`.
We use `extendUpdatedVars c₁ ws` and `extendUpdatedVars c₂ ws`
-/
def homogenize (c₁ c₂ : CodeBlock) : TermElabM (CodeBlock × CodeBlock) := do
  let ws := union c₁.uvars c₂.uvars
  let c₁ ← extendUpdatedVars c₁ ws
  let c₂ ← extendUpdatedVars c₂ ws
  pure (c₁, c₂)

/--
Extending code blocks with variable declarations: `let x : t := v` and `let x : t ← v`.
We remove `x` from the collection of updated variables.
Remark: `stx` is the syntax for the declaration (e.g., `letDecl`), and `xs` are the variables
declared by it. It is an array because we have let-declarations that declare multiple variables.
Example: `let (x, y) := t`
-/
def mkVarDeclCore (xs : Array Var) (stx : Syntax) (c : CodeBlock) : CodeBlock := {
  code := Code.decl xs stx c.code,
  uvars := eraseVars c.uvars xs
}

/--
Extending code blocks with reassignments: `x : t := v` and `x : t ← v`.
Remark: `stx` is the syntax for the declaration (e.g., `letDecl`), and `xs` are the variables
declared by it. It is an array because we have let-declarations that declare multiple variables.
Example: `(x, y) ← t`
-/
def mkReassignCore (xs : Array Var) (stx : Syntax) (c : CodeBlock) : TermElabM CodeBlock := do
  let us := c.uvars
  let ws := insertVars us xs
  -- If `xs` contains a new updated variable, then we must use `extendUpdatedVars`.
  -- See discussion at `pullExitPoints`
  let code ← if xs.any fun x => !us.contains x.getId then extendUpdatedVarsAux c.code ws else pure c.code
  pure { code := .reassign xs stx code, uvars := ws }

def mkSeq (action : Syntax) (c : CodeBlock) : CodeBlock :=
  { c with code := .seq action c.code }

def mkTerminalAction (action : Syntax) : CodeBlock :=
  { code := .action action }

def mkReturn (ref : Syntax) (val : Syntax) : CodeBlock :=
  { code := .return ref val }

def mkBreak (ref : Syntax) : CodeBlock :=
  { code := .break ref }

def mkContinue (ref : Syntax) : CodeBlock :=
  { code := .continue ref }

def mkIte (ref : Syntax) (optIdent : Syntax) (cond : Syntax) (thenBranch : CodeBlock) (elseBranch : CodeBlock) : TermElabM CodeBlock := do
  let x? := optIdent.getOptional?
  let (thenBranch, elseBranch) ← homogenize thenBranch elseBranch
  return {
    code  := .ite ref x? optIdent cond thenBranch.code elseBranch.code,
    uvars := thenBranch.uvars,
  }

private def mkUnit : MacroM Syntax :=
  ``((⟨⟩ : PUnit))

private def mkPureUnit : MacroM Syntax :=
  ``(pure PUnit.unit)

def mkPureUnitAction : MacroM CodeBlock := do
  return mkTerminalAction (← mkPureUnit)

def mkUnless (cond : Syntax) (c : CodeBlock) : MacroM CodeBlock := do
  let thenBranch ← mkPureUnitAction
  return { c with code := .ite (← getRef) none mkNullNode cond thenBranch.code c.code }

def mkMatch (ref : Syntax) (genParam : Syntax) (discrs : Syntax) (optMotive : Syntax) (alts : Array (Alt CodeBlock)) : TermElabM CodeBlock := do
  -- nary version of homogenize
  let ws := alts.foldl (union · ·.rhs.uvars) {}
  let alts ← alts.mapM fun alt => do
    let rhs ← extendUpdatedVars alt.rhs ws
    return { ref := alt.ref, vars := alt.vars, patterns := alt.patterns, rhs := rhs.code : Alt Code }
  return { code := .match ref genParam discrs optMotive alts, uvars := ws }

/-- Return a code block that executes `terminal` and then `k` with the value produced by `terminal`.
   This method assumes `terminal` is a terminal -/
def concat (terminal : CodeBlock) (kRef : Syntax) (y? : Option Var) (k : CodeBlock) : TermElabM CodeBlock := do
  unless hasTerminalAction terminal.code do
    throwErrorAt kRef "`do` element is unreachable"
  let (terminal, k) ← homogenize terminal k
  let xs := varSetToArray k.uvars
  let y ← match y? with | some y => pure y | none => `(y)
  let ps := xs.map fun x => (x, true)
  let ps := ps.push (y, false)
  let jpDecl ← mkFreshJP ps k.code
  let jp := jpDecl.name
  let terminal ← liftMacroM <| convertTerminalActionIntoJmp terminal.code jp xs
  return { code  := attachJP jpDecl terminal, uvars := k.uvars }

def getLetIdDeclVars (letIdDecl : Syntax) : Array Var :=
  if letIdDecl[0].isIdent then
    #[letIdDecl[0]]
  else
    #[]

-- support both regular and syntax match
def getPatternVarsEx (pattern : Syntax) : TermElabM (Array Var) :=
  getPatternVars pattern <|>
  Quotation.getPatternVars pattern

def getPatternsVarsEx (patterns : Array Syntax) : TermElabM (Array Var) :=
  getPatternsVars patterns <|>
  Quotation.getPatternsVars patterns

def getLetPatDeclVars (letPatDecl : Syntax) : TermElabM (Array Var) := do
  let pattern := letPatDecl[0]
  getPatternVarsEx pattern

def getLetEqnsDeclVars (letEqnsDecl : Syntax) : Array Var :=
  if letEqnsDecl[0].isIdent then
    #[letEqnsDecl[0]]
  else
    #[]

def getLetDeclVars (letDecl : Syntax) : TermElabM (Array Var) := do
  let arg := letDecl[0]
  if arg.getKind == ``Parser.Term.letIdDecl then
    return getLetIdDeclVars arg
  else if arg.getKind == ``Parser.Term.letPatDecl then
    getLetPatDeclVars arg
  else if arg.getKind == ``Parser.Term.letEqnsDecl then
    return getLetEqnsDeclVars arg
  else
    throwError "unexpected kind of let declaration"

def getDoLetVars (doLet : Syntax) : TermElabM (Array Var) :=
  -- leading_parser "let " >> optional "mut " >> letDecl
  getLetDeclVars doLet[2]

def getHaveIdLhsVar (optIdent : Syntax) : Var :=
  if optIdent.getKind == hygieneInfoKind then
    HygieneInfo.mkIdent optIdent[0] `this
  else
    optIdent

def getDoHaveVars (doHave : Syntax) : TermElabM (Array Var) := do
  -- doHave := leading_parser "have " >> Term.haveDecl
  -- haveDecl := leading_parser haveIdDecl <|> letPatDecl <|> haveEqnsDecl
  let arg := doHave[1][0]
  if arg.getKind == ``Parser.Term.haveIdDecl then
    -- haveIdDecl := leading_parser atomic (haveIdLhs >> " := ") >> termParser
    -- haveIdLhs := (binderIdent <|> hygieneInfo) >> many letIdBinder >> optType
    return #[getHaveIdLhsVar arg[0]]
  else if arg.getKind == ``Parser.Term.letPatDecl then
    getLetPatDeclVars arg
  else if arg.getKind == ``Parser.Term.haveEqnsDecl then
    -- haveEqnsDecl := leading_parser haveIdLhs >> matchAlts
    return #[getHaveIdLhsVar arg[0]]
  else
    throwError "unexpected kind of have declaration"

def getDoLetRecVars (doLetRec : Syntax) : TermElabM (Array Var) := do
  -- letRecDecls is an array of `(group (optional attributes >> letDecl))`
  let letRecDecls := doLetRec[1][0].getSepArgs
  let letDecls := letRecDecls.map fun p => p[2]
  let mut allVars := #[]
  for letDecl in letDecls do
    let vars ← getLetDeclVars letDecl
    allVars := allVars ++ vars
  return allVars

-- ident >> optType >> leftArrow >> termParser
def getDoIdDeclVar (doIdDecl : Syntax) : Var :=
  doIdDecl[0]

-- termParser >> leftArrow >> termParser >> optional (" | " >> termParser)
def getDoPatDeclVars (doPatDecl : Syntax) : TermElabM (Array Var) := do
  let pattern := doPatDecl[0]
  getPatternVarsEx pattern

-- leading_parser "let " >> optional "mut " >> (doIdDecl <|> doPatDecl)
def getDoLetArrowVars (doLetArrow : Syntax) : TermElabM (Array Var) := do
  let decl := doLetArrow[2]
  if decl.getKind == ``Parser.Term.doIdDecl then
    return #[getDoIdDeclVar decl]
  else if decl.getKind == ``Parser.Term.doPatDecl then
    getDoPatDeclVars decl
  else
    throwError "unexpected kind of `do` declaration"

def getDoReassignVars (doReassign : Syntax) : TermElabM (Array Var) := do
  let arg := doReassign[0]
  if arg.getKind == ``Parser.Term.letIdDecl then
    return getLetIdDeclVars arg
  else if arg.getKind == ``Parser.Term.letPatDecl then
    getLetPatDeclVars arg
  else
    throwError "unexpected kind of reassignment"

def mkDoSeq (doElems : Array Syntax) : Syntax :=
  mkNode `Lean.Parser.Term.doSeqIndent #[mkNullNode <| doElems.map fun doElem => mkNullNode #[doElem, mkNullNode]]

/--
  If the given syntax is a `doIf`, return an equivalent `doIf` that has an `else` but no `else if`s or `if let`s.  -/
private def expandDoIf? (stx : Syntax) : MacroM (Option Syntax) := match stx with
  | `(doElem|if $_:doIfProp then $_ else $_) => pure none
  | `(doElem|if $cond:doIfCond then $t $[else if $conds:doIfCond then $ts]* $[else $e?]?) => withRef stx do
    let mut e      := e?.getD (← `(doSeq|pure PUnit.unit))
    let mut eIsSeq := true
    for (cond, t) in Array.zip (conds.reverse.push cond) (ts.reverse.push t) do
      e ← if eIsSeq then pure e else `(doSeq|$e:doElem)
      e ← match cond with
        | `(doIfCond|let $pat := $d) => `(doElem| match $d:term with | $pat:term => $t | _ => $e)
        | `(doIfCond|let $pat ← $d)  => `(doElem| match ← $d    with | $pat:term => $t | _ => $e)
        | `(doIfCond|$cond:doIfProp) => `(doElem| if $cond:doIfProp then $t else $e)
        | _                          => `(doElem| if $(Syntax.missing) then $t else $e)
      eIsSeq := false
    return some e
  | _ => pure none

structure DoIfView where
  ref        : Syntax
  optIdent   : Syntax
  cond       : Syntax
  thenBranch : Syntax
  elseBranch : Syntax

/-- This method assumes `expandDoIf?` is not applicable. -/
private def mkDoIfView (doIf : Syntax) : DoIfView := {
  ref        := doIf
  optIdent   := doIf[1][0]
  cond       := doIf[1][1]
  thenBranch := doIf[3]
  elseBranch := doIf[5][1]
}

/--
We use `MProd` instead of `Prod` to group values when expanding the
`do` notation. `MProd` is a universe monomorphic product.
The motivation is to generate simpler universe constraints in code
that was not written by the user.
Note that we are not restricting the macro power since the
`Bind.bind` combinator already forces values computed by monadic
actions to be in the same universe.
-/
private def mkTuple (elems : Array Syntax) : MacroM Syntax := do
  if elems.size == 0 then
    mkUnit
  else if elems.size == 1 then
    return elems[0]!
  else
    elems.extract 0 (elems.size - 1) |>.foldrM (init := elems.back) fun elem tuple =>
      ``(MProd.mk $elem $tuple)

/-- Return `some action` if `doElem` is a `doExpr <action>`-/
def isDoExpr? (doElem : Syntax) : Option Syntax :=
  if doElem.getKind == ``Parser.Term.doExpr then
    some doElem[0]
  else
    none

/--
  Given `uvars := #[a_1, ..., a_n, a_{n+1}]` construct term
  ```
  let a_1     := x.1
  let x       := x.2
  let a_2     := x.1
  let x       := x.2
  ...
  let a_n     := x.1
  let a_{n+1} := x.2
  body
  ```
  Special cases
  - `uvars := #[]` => `body`
  - `uvars := #[a]` => `let a := x; body`


  We use this method when expanding the `for-in` notation.
-/
private def destructTuple (uvars : Array Var) (x : Syntax) (body : Syntax) : MacroM Syntax := do
  if uvars.size == 0 then
    return body
  else if uvars.size == 1 then
    `(let $(uvars[0]!):ident := $x; $body)
  else
    destruct uvars.toList x body
where
  destruct (as : List Var) (x : Syntax) (body : Syntax) : MacroM Syntax := do
    match as with
      | [a, b]  => `(let $a:ident := $x.1; let $b:ident := $x.2; $body)
      | a :: as => withFreshMacroScope do
        let rest ← destruct as (← `(x)) body
        `(let $a:ident := $x.1; let x := $x.2; $rest)
      | _ => unreachable!

/-!
The procedure `ToTerm.run` converts a `CodeBlock` into a `Syntax` term.
We use this method to convert
1- The `CodeBlock` for a root `do ...` term into a `Syntax` term. This kind of
   `CodeBlock` never contains `break` nor `continue`. Moreover, the collection
   of updated variables is not packed into the result.
   Thus, we have two kinds of exit points
     - `Code.action e` which is converted into `e`
     - `Code.return _ e` which is converted into `pure e`

   We use `Kind.regular` for this case.

2- The `CodeBlock` for `b` at `for x in xs do b`. In this case, we need to generate
   a `Syntax` term representing a function for the `xs.forIn` combinator.

   a) If `b` contain a `Code.return _ a` exit point. The generated `Syntax` term
      has type `m (ForInStep (Option α × σ))`, where `a : α`, and the `σ` is the type
      of the tuple of variables reassigned by `b`.
      We use `Kind.forInWithReturn` for this case

   b) If `b` does not contain a `Code.return _ a` exit point. Then, the generated
      `Syntax` term has type `m (ForInStep σ)`.
      We use `Kind.forIn` for this case.

3- The `CodeBlock` `c` for a `do` sequence nested in a monadic combinator (e.g., `MonadExcept.tryCatch`).

   The generated `Syntax` term for `c` must inform whether `c` "exited" using `Code.action`, `Code.return`,
   `Code.break` or `Code.continue`. We use the auxiliary types `DoResult`s for storing this information.
   For example, the auxiliary type `DoResultPBC α σ` is used for a code block that exits with `Code.action`,
   **and** `Code.break`/`Code.continue`, `α` is the type of values produced by the exit `action`, and
   `σ` is the type of the tuple of reassigned variables.
   The type `DoResult α β σ` is usedf for code blocks that exit with
   `Code.action`, `Code.return`, **and** `Code.break`/`Code.continue`, `β` is the type of the returned values.
   We don't use `DoResult α β σ` for all cases because:

      a) The elaborator would not be able to infer all type parameters without extra annotations. For example,
         if the code block does not contain `Code.return _ _`, the elaborator will not be able to infer `β`.

      b) We need to pattern match on the result produced by the combinator (e.g., `MonadExcept.tryCatch`),
         but we don't want to consider "unreachable" cases.

   We do not distinguish between cases that contain `break`, but not `continue`, and vice versa.

   When listing all cases, we use `a` to indicate the code block contains `Code.action _`, `r` for `Code.return _ _`,
   and `b/c` for a code block that contains `Code.break _` or `Code.continue _`.

   - `a`: `Kind.regular`, type `m (α × σ)`

   - `r`: `Kind.regular`, type `m (α × σ)`
           Note that the code that pattern matches on the result will behave differently in this case.
           It produces `return a` for this case, and `pure a` for the previous one.

   - `b/c`: `Kind.nestedBC`, type `m (DoResultBC σ)`

   - `a` and `r`:   `Kind.nestedPR`, type `m (DoResultPR α β σ)`

   - `a` and `bc`:  `Kind.nestedSBC`, type `m (DoResultSBC α σ)`

   - `r` and `bc`:  `Kind.nestedSBC`, type `m (DoResultSBC α σ)`
         Again the code that pattern matches on the result will behave differently in this case and
         the previous one. It produces `return a` for the constructor `DoResultSPR.pureReturn a u` for
         this case, and `pure a` for the previous case.

   - `a`, `r`, `b/c`: `Kind.nestedPRBC`, type type `m (DoResultPRBC α β σ)`

Here is the recipe for adding new combinators with nested `do`s.
Example: suppose we want to support `repeat doSeq`. Assuming we have `repeat : m α → m α`
1- Convert `doSeq` into `codeBlock : CodeBlock`
2- Create term `term` using `mkNestedTerm code m uvars a r bc` where
   `code` is `codeBlock.code`, `uvars` is an array containing `codeBlock.uvars`,
   `m` is a `Syntax` representing the Monad, and
   `a` is true if `code` contains `Code.action _`,
   `r` is true if `code` contains `Code.return _ _`,
   `bc` is true if `code` contains `Code.break _` or `Code.continue _`.

   Remark: for combinators such as `repeat` that take a single `doSeq`, all
   arguments, but `m`, are extracted from `codeBlock`.
3- Create the term `repeat $term`
4- and then, convert it into a `doSeq` using `matchNestedTermResult ref (repeat $term) uvsar a r bc`

-/

/--
Helper method for annotating `term` with the raw syntax `ref`.
We use this method to implement finer-grained term infos for `do`-blocks.

We use `withRef term` to make sure the synthetic position for the `with_annotate_term` is equal
to the one for `term`. This is important for producing error messages when there is a type mismatch.
Consider the following example:
```
opaque f : IO Nat

def g : IO String := do
  f
```
There is at type mismatch at `f`, but it is detected when elaborating the expanded term
containing the `with_annotate_term .. f`. The current `getRef` when this `annotate` is invoked
is not necessarily `f`. Actually, it is the whole `do`-block. By using `withRef` we ensure
the synthetic position for the `with_annotate_term ..` is equal to `term`.
Recall that synthetic positions are used when generating error messages.
-/
def annotate [Monad m] [MonadRef m] [MonadQuotation m] (ref : Syntax) (term : Syntax) : m Syntax :=
  withRef term <| `(with_annotate_term $ref $term)

namespace ToTerm

inductive Kind where
  | regular
  | forIn
  | forInWithReturn
  | nestedBC
  | nestedPR
  | nestedSBC
  | nestedPRBC

instance : Inhabited Kind := ⟨Kind.regular⟩

def Kind.isRegular : Kind → Bool
  | .regular => true
  | _        => false

structure Context where
  /-- Syntax to reference the monad associated with the do notation. -/
  m          : Syntax
  /-- Syntax to reference the result of the monadic computation performed by the do notation. -/
  returnType : Syntax
  uvars      : Array Var
  kind       : Kind

abbrev M := ReaderT Context MacroM

def mkUVarTuple : M Syntax := do
  let ctx ← read
  mkTuple ctx.uvars

def returnToTerm (val : Syntax) : M Syntax := do
  let ctx ← read
  let u ← mkUVarTuple
  match ctx.kind with
  | .regular         => if ctx.uvars.isEmpty then ``(Pure.pure $val) else ``(Pure.pure (MProd.mk $val $u))
  | .forIn           => ``(Pure.pure (ForInStep.done $u))
  | .forInWithReturn => ``(Pure.pure (ForInStep.done (MProd.mk (some $val) $u)))
  | .nestedBC        => unreachable!
  | .nestedPR        => ``(Pure.pure (DoResultPR.«return» $val $u))
  | .nestedSBC       => ``(Pure.pure (DoResultSBC.«pureReturn» $val $u))
  | .nestedPRBC      => ``(Pure.pure (DoResultPRBC.«return» $val $u))

def continueToTerm : M Syntax := do
  let ctx ← read
  let u ← mkUVarTuple
  match ctx.kind with
  | .regular         => unreachable!
  | .forIn           => ``(Pure.pure (ForInStep.yield $u))
  | .forInWithReturn => ``(Pure.pure (ForInStep.yield (MProd.mk none $u)))
  | .nestedBC        => ``(Pure.pure (DoResultBC.«continue» $u))
  | .nestedPR        => unreachable!
  | .nestedSBC       => ``(Pure.pure (DoResultSBC.«continue» $u))
  | .nestedPRBC      => ``(Pure.pure (DoResultPRBC.«continue» $u))

def breakToTerm : M Syntax := do
  let ctx ← read
  let u ← mkUVarTuple
  match ctx.kind with
  | .regular         => unreachable!
  | .forIn           => ``(Pure.pure (ForInStep.done $u))
  | .forInWithReturn => ``(Pure.pure (ForInStep.done (MProd.mk none $u)))
  | .nestedBC        => ``(Pure.pure (DoResultBC.«break» $u))
  | .nestedPR        => unreachable!
  | .nestedSBC       => ``(Pure.pure (DoResultSBC.«break» $u))
  | .nestedPRBC      => ``(Pure.pure (DoResultPRBC.«break» $u))

def actionTerminalToTerm (action : Syntax) : M Syntax := withRef action <| withFreshMacroScope do
  let ctx ← read
  let u ← mkUVarTuple
  match ctx.kind with
  | .regular         => if ctx.uvars.isEmpty then pure action else ``(Bind.bind $action fun y => Pure.pure (MProd.mk y $u))
  | .forIn           => ``(Bind.bind $action fun (_ : PUnit) => Pure.pure (ForInStep.yield $u))
  | .forInWithReturn => ``(Bind.bind $action fun (_ : PUnit) => Pure.pure (ForInStep.yield (MProd.mk none $u)))
  | .nestedBC        => unreachable!
  | .nestedPR        => ``(Bind.bind $action fun y => (Pure.pure (DoResultPR.«pure» y $u)))
  | .nestedSBC       => ``(Bind.bind $action fun y => (Pure.pure (DoResultSBC.«pureReturn» y $u)))
  | .nestedPRBC      => ``(Bind.bind $action fun y => (Pure.pure (DoResultPRBC.«pure» y $u)))

def seqToTerm (action : Syntax) (k : Syntax) : M Syntax := withRef action <| withFreshMacroScope do
  if action.getKind == ``Parser.Term.doDbgTrace then
    let msg := action[1]
    `(dbg_trace $msg; $k)
  else if action.getKind == ``Parser.Term.doAssert then
    let cond := action[1]
    `(assert! $cond; $k)
  else
    let action ← withRef action ``(($action : $((←read).m) PUnit))
    ``(Bind.bind $action (fun (_ : PUnit) => $k))

def declToTerm (decl : Syntax) (k : Syntax) : M Syntax := withRef decl <| withFreshMacroScope do
  let kind := decl.getKind
  if kind == ``Parser.Term.doLet then
    let letDecl := decl[2]
    `(let $letDecl:letDecl; $k)
  else if kind == ``Parser.Term.doLetRec then
    let letRecToken := decl[0]
    let letRecDecls := decl[1]
    return mkNode ``Parser.Term.letrec #[letRecToken, letRecDecls, mkNullNode, k]
  else if kind == ``Parser.Term.doLetArrow then
    let arg := decl[2]
    if arg.getKind == ``Parser.Term.doIdDecl then
      let id     := arg[0]
      let type   := expandOptType id arg[1]
      let doElem := arg[3]
      -- `doElem` must be a `doExpr action`. See `doLetArrowToCode`
      match isDoExpr? doElem with
      | some action =>
        let action ← withRef action `(($action : $((← read).m) $type))
        ``(Bind.bind $action (fun ($id:ident : $type) => $k))
      | none        => Macro.throwErrorAt decl "unexpected kind of `do` declaration"
    else
      Macro.throwErrorAt decl "unexpected kind of `do` declaration"
  else if kind == ``Parser.Term.doHave then
    -- The `have` term is of the form  `"have " >> haveDecl >> optSemicolon termParser`
    let args := decl.getArgs
    let args := args ++ #[mkNullNode /- optional ';' -/, k]
    return mkNode `Lean.Parser.Term.«have» args
  else
    Macro.throwErrorAt decl "unexpected kind of `do` declaration"

def reassignToTerm (reassign : Syntax) (k : Syntax) : MacroM Syntax := withRef reassign <| withFreshMacroScope do
  match reassign with
  | `(doElem| $x:ident := $rhs) => `(let $x:ident := ensure_type_of% $x $(quote "invalid reassignment, value") $rhs; $k)
  | `(doElem| $e:term  := $rhs) => `(let $e:term  := ensure_type_of% $e $(quote "invalid reassignment, value") $rhs; $k)
  | _ =>
    -- Note that `doReassignArrow` is expanded by `doReassignArrowToCode
    Macro.throwErrorAt reassign "unexpected kind of `do` reassignment"

def mkIte (optIdent : Syntax) (cond : Syntax) (thenBranch : Syntax) (elseBranch : Syntax) : MacroM Syntax := do
  if optIdent.isNone then
    ``(if $cond then $thenBranch else $elseBranch)
  else
    let h := optIdent[0]
    ``(if $h:ident : $cond then $thenBranch else $elseBranch)

def mkJoinPoint (j : Name) (ps : Array (Syntax × Bool)) (body : Syntax) (k : Syntax) : M Syntax := withRef body <| withFreshMacroScope do
  let pTypes ← ps.mapM fun ⟨id, useTypeOf⟩ => do if useTypeOf then `(type_of% $id) else `(_)
  let ps     := ps.map (·.1)
  /-
  We use `let_delayed` instead of `let` for joinpoints to make sure `$k` is elaborated before `$body`.
  By elaborating `$k` first, we "learn" more about `$body`'s type.
  For example, consider the following example `do` expression
  ```
  def f (x : Nat) : IO Unit := do
  if x > 0 then
    IO.println "x is not zero" -- Error is here
  IO.mkRef true
  ```
  it is expanded into
  ```
  def f (x : Nat) : IO Unit := do
  let jp (u : Unit) : IO _ :=
    IO.mkRef true;
  if x > 0 then
    IO.println "not zero"
    jp ()
  else
    jp ()
  ```
  If we use the regular `let` instead of `let_delayed`, the joinpoint `jp` will be elaborated and its type will be inferred to be `Unit → IO (IO.Ref Bool)`.
  Then, we get a typing error at `jp ()`. By using `let_delayed`, we first elaborate `if x > 0 ...` and learn that `jp` has type `Unit → IO Unit`.
  Then, we get the expected type mismatch error at `IO.mkRef true`. -/
  `(let_delayed $(← mkIdentFromRef j):ident $[($ps : $pTypes)]* : $((← read).m) _ := $body; $k)

def mkJmp (ref : Syntax) (j : Name) (args : Array Syntax) : Syntax :=
  Syntax.mkApp (mkIdentFrom ref j) args

partial def toTerm (c : Code) : M Syntax := do
  let term ← go c
  if let some ref := c.getRef? then
    annotate ref term
  else
    return term
where
  go (c : Code) : M Syntax := do
    match c with
    | .return ref val     => withRef ref <| returnToTerm val
    | .continue ref       => withRef ref continueToTerm
    | .break ref          => withRef ref breakToTerm
    | .action e           => actionTerminalToTerm e
    | .joinpoint j ps b k => mkJoinPoint j ps (← toTerm b) (← toTerm k)
    | .jmp ref j args     => return mkJmp ref j args
    | .decl _ stx k       => declToTerm stx (← toTerm k)
    | .reassign _ stx k   => reassignToTerm stx (← toTerm k)
    | .seq stx k          => seqToTerm stx (← toTerm k)
    | .ite ref _ o c t e  => withRef ref <| do mkIte o c (← toTerm t) (← toTerm e)
    | .match ref genParam discrs optMotive alts =>
      let mut termAlts := #[]
      for alt in alts do
        let rhs ← toTerm alt.rhs
        let termAlt := mkNode `Lean.Parser.Term.matchAlt #[mkAtomFrom alt.ref "|", mkNullNode #[alt.patterns], mkAtomFrom alt.ref "=>", rhs]
        termAlts := termAlts.push termAlt
      let termMatchAlts := mkNode `Lean.Parser.Term.matchAlts #[mkNullNode termAlts]
      return mkNode `Lean.Parser.Term.«match» #[mkAtomFrom ref "match", genParam, optMotive, discrs, mkAtomFrom ref "with", termMatchAlts]

def run (code : Code) (m : Syntax) (returnType : Syntax) (uvars : Array Var := #[]) (kind := Kind.regular) : MacroM Syntax :=
  toTerm code { m, returnType, kind, uvars }

/-- Given
   - `a` is true if the code block has a `Code.action _` exit point
   - `r` is true if the code block has a `Code.return _ _` exit point
   - `bc` is true if the code block has a `Code.break _` or `Code.continue _` exit point

   generate Kind. See comment at the beginning of the `ToTerm` namespace. -/
def mkNestedKind (a r bc : Bool) : Kind :=
  match a, r, bc with
  | true,  false, false => .regular
  | false, true,  false => .regular
  | false, false, true  => .nestedBC
  | true,  true,  false => .nestedPR
  | true,  false, true  => .nestedSBC
  | false, true,  true  => .nestedSBC
  | true,  true,  true  => .nestedPRBC
  | false, false, false => unreachable!

def mkNestedTerm (code : Code) (m : Syntax) (returnType : Syntax) (uvars : Array Var) (a r bc : Bool) : MacroM Syntax := do
  ToTerm.run code m returnType uvars (mkNestedKind a r bc)

/-- Given a term `term` produced by `ToTerm.run`, pattern match on its result.
   See comment at the beginning of the `ToTerm` namespace.

   - `a` is true if the code block has a `Code.action _` exit point
   - `r` is true if the code block has a `Code.return _ _` exit point
   - `bc` is true if the code block has a `Code.break _` or `Code.continue _` exit point

   The result is a sequence of `doElem` -/
def matchNestedTermResult (term : Syntax) (uvars : Array Var) (a r bc : Bool) : MacroM (List Syntax) := do
  let toDoElems (auxDo : Syntax) : List Syntax := getDoSeqElems (getDoSeq auxDo)
  let u ← mkTuple uvars
  match a, r, bc with
  | true, false, false =>
    if uvars.isEmpty then
      return toDoElems (← `(do $term:term))
    else
      return toDoElems (← `(do let r ← $term:term; $u:term := r.2; pure r.1))
  | false, true, false =>
    if uvars.isEmpty then
      return toDoElems (← `(do let r ← $term:term; return r))
    else
      return toDoElems (← `(do let r ← $term:term; $u:term := r.2; return r.1))
  | false, false, true => toDoElems <$>
    `(do let r ← $term:term;
         match r with
         | .break u => $u:term := u; break
         | .continue u => $u:term := u; continue)
  | true, true, false => toDoElems <$>
    `(do let r ← $term:term;
         match r with
         | .pure a u => $u:term := u; pure a
         | .return b u => $u:term := u; return b)
  | true, false, true => toDoElems <$>
    `(do let r ← $term:term;
         match r with
         | .pureReturn a u => $u:term := u; pure a
         | .break u => $u:term := u; break
         | .continue u => $u:term := u; continue)
  | false, true, true => toDoElems <$>
    `(do let r ← $term:term;
         match r with
         | .pureReturn a u => $u:term := u; return a
         | .break u => $u:term := u; break
         | .continue u => $u:term := u; continue)
  | true, true, true => toDoElems <$>
    `(do let r ← $term:term;
         match r with
         | .pure a u => $u:term := u; pure a
         | .return a u => $u:term := u; return a
         | .break u => $u:term := u; break
         | .continue u => $u:term := u; continue)
  | false, false, false => unreachable!

end ToTerm

def isMutableLet (doElem : Syntax) : Bool :=
  let kind := doElem.getKind
  (kind == ``doLetArrow || kind == ``doLet || kind == ``doLetElse)
  &&
  !doElem[1].isNone

namespace ToCodeBlock

structure Context where
  ref         : Syntax
  /-- Syntax representing the monad associated with the do notation. -/
  m           : Syntax
  /-- Syntax to reference the result of the monadic computation performed by the do notation. -/
  returnType  : Syntax
  mutableVars : VarSet := {}
  insideFor   : Bool := false

abbrev M := ReaderT Context TermElabM

def withNewMutableVars {α} (newVars : Array Var) (mutable : Bool) (x : M α) : M α :=
  withReader (fun ctx => if mutable then { ctx with mutableVars := insertVars ctx.mutableVars newVars } else ctx) x

def checkReassignable (xs : Array Var) : M Unit := do
  let throwInvalidReassignment (x : Name) : M Unit :=
    throwError "`{x.simpMacroScopes}` cannot be mutated, only variables declared using `let mut` can be mutated. If you did not intent to mutate but define `{x.simpMacroScopes}`, consider using `let {x.simpMacroScopes}` instead"
  let ctx ← read
  for x in xs do
    unless ctx.mutableVars.contains x.getId do
      throwInvalidReassignment x.getId

def checkNotShadowingMutable (xs : Array Var) : M Unit := do
  let throwInvalidShadowing (x : Name) : M Unit :=
    throwError "mutable variable `{x.simpMacroScopes}` cannot be shadowed"
  let ctx ← read
  for x in xs do
    if ctx.mutableVars.contains x.getId then
      withRef x <| throwInvalidShadowing x.getId

def withFor {α} (x : M α) : M α :=
  withReader (fun ctx => { ctx with insideFor := true }) x

structure ToForInTermResult where
  uvars      : Array Var
  term       : Syntax

def mkForInBody  (_ : Syntax) (forInBody : CodeBlock) : M ToForInTermResult := do
  let ctx ← read
  let uvars := forInBody.uvars
  let uvars := varSetToArray uvars
  let term ← liftMacroM <| ToTerm.run forInBody.code ctx.m ctx.returnType uvars (if hasReturn forInBody.code then ToTerm.Kind.forInWithReturn else ToTerm.Kind.forIn)
  return ⟨uvars, term⟩

def ensureInsideFor : M Unit :=
  unless (← read).insideFor do
    throwError "invalid `do` element, it must be inside `for`"

def ensureEOS (doElems : List Syntax) : M Unit :=
  unless doElems.isEmpty do
    throwError "must be last element in a `do` sequence"

variable (baseId : Name) in
private partial def expandLiftMethodAux (inQuot : Bool) (inBinder : Bool) : Syntax → StateT (List Syntax) M Syntax
  | stx@(Syntax.node i k args) =>
    if k == choiceKind then do
      -- choice node: check that lifts are consistent
      let alts ← stx.getArgs.mapM (expandLiftMethodAux inQuot inBinder · |>.run [])
      let (_, lifts) := alts[0]!
      unless alts.all (·.2 == lifts) do
        throwErrorAt stx "cannot lift `(<- ...)` over inconsistent syntax variants, consider lifting out the binding manually"
      modify (· ++ lifts)
      return .node i k (alts.map (·.1))
    else if liftMethodDelimiter k then
      return stx
    else if k == ``Parser.Term.liftMethod && !inQuot then withFreshMacroScope do
      if inBinder then
        throwErrorAt stx "cannot lift `(<- ...)` over a binder, this error usually happens when you are trying to lift a method nested in a `fun`, `let`, or `match`-alternative, and it can often be fixed by adding a missing `do`"
      let term := args[1]!
      let term ← expandLiftMethodAux inQuot inBinder term
      -- keep name deterministic across choice branches
      let id ← mkIdentFromRef (.num baseId (← get).length)
      let auxDoElem : Syntax ← `(doElem| let $id:ident ← $term:term)
      modify fun s => s ++ [auxDoElem]
      return id
    else do
      let inAntiquot := stx.isAntiquot && !stx.isEscapedAntiquot
      let inBinder   := inBinder || (!inQuot && liftMethodForbiddenBinder stx)
      let args ← args.mapM (expandLiftMethodAux (inQuot && !inAntiquot || stx.isQuot) inBinder)
      return Syntax.node i k args
  | stx => return stx

def expandLiftMethod (doElem : Syntax) : M (List Syntax × Syntax) := do
  if !hasLiftMethod doElem then
    return ([], doElem)
  else
    let baseId ← withFreshMacroScope (MonadQuotation.addMacroScope `__do_lift)
    let (doElem, doElemsNew) ← (expandLiftMethodAux baseId false false doElem).run []
    return (doElemsNew, doElem)

def checkLetArrowRHS (doElem : Syntax) : M Unit := do
  let kind := doElem.getKind
  if kind == ``Parser.Term.doLetArrow ||
     kind == ``Parser.Term.doLet ||
     kind == ``Parser.Term.doLetRec ||
     kind == ``Parser.Term.doHave ||
     kind == ``Parser.Term.doReassign ||
     kind == ``Parser.Term.doReassignArrow then
    throwErrorAt doElem "invalid kind of value `{kind}` in an assignment"

/-- Generate `CodeBlock` for `doReturn` which is of the form
   ```
   "return " >> optional termParser
   ```
   `doElems` is only used for sanity checking. -/
def doReturnToCode (doReturn : Syntax) (doElems: List Syntax) : M CodeBlock := withRef doReturn do
  ensureEOS doElems
  let argOpt := doReturn[1]
  let arg ← if argOpt.isNone then liftMacroM mkUnit else pure argOpt[0]
  return mkReturn (← getRef) arg

structure Catch where
  x         : Syntax
  optType   : Syntax
  codeBlock : CodeBlock

def getTryCatchUpdatedVars (tryCode : CodeBlock) (catches : Array Catch) (finallyCode? : Option CodeBlock) : VarSet :=
  let ws := tryCode.uvars
  let ws := catches.foldl (init := ws) fun ws alt => union alt.codeBlock.uvars ws
  let ws := match finallyCode? with
    | none   => ws
    | some c => union c.uvars ws
  ws

def tryCatchPred (tryCode : CodeBlock) (catches : Array Catch) (finallyCode? : Option CodeBlock) (p : Code → Bool) : Bool :=
  p tryCode.code ||
  catches.any (fun «catch» => p «catch».codeBlock.code) ||
  match finallyCode? with
  | none => false
  | some finallyCode => p finallyCode.code

mutual
  /-- "Concatenate" `c` with `doSeqToCode doElems` -/
  partial def concatWith (c : CodeBlock) (doElems : List Syntax) : M CodeBlock :=
    match doElems with
    | [] => pure c
    | nextDoElem :: _  => do
      let k ← doSeqToCode doElems
      let ref := nextDoElem
      concat c ref none k

  /-- Generate `CodeBlock` for `doLetArrow; doElems`
     `doLetArrow` is of the form
     ```
     "let " >> optional "mut " >> (doIdDecl <|> doPatDecl)
     ```
     where
     ```
     def doIdDecl   := leading_parser ident >> optType >> leftArrow >> doElemParser
     def doPatDecl  := leading_parser termParser >> leftArrow >> doElemParser >> optional (" | " >> doSeq)
     ```
  -/
  partial def doLetArrowToCode (doLetArrow : Syntax) (doElems : List Syntax) : M CodeBlock := do
    let decl    := doLetArrow[2]
    if decl.getKind == ``Parser.Term.doIdDecl then
      let y := decl[0]
      checkNotShadowingMutable #[y]
      let doElem := decl[3]
      let k ← withNewMutableVars #[y] (isMutableLet doLetArrow) (doSeqToCode doElems)
      match isDoExpr? doElem with
      | some _      => return mkVarDeclCore #[y] doLetArrow k
      | none =>
        checkLetArrowRHS doElem
        let c ← doSeqToCode [doElem]
        match doElems with
        | []       => pure c
        | kRef::_  => concat c kRef y k
    else if decl.getKind == ``Parser.Term.doPatDecl then
      let pattern := decl[0]
      let doElem  := decl[2]
      let optElse := decl[3]
      if optElse.isNone then withFreshMacroScope do
        let auxDo ← if isMutableLet doLetArrow then
          `(do let%$doLetArrow __discr ← $doElem; let%$doLetArrow mut $pattern:term := __discr)
        else
          `(do let%$doLetArrow __discr ← $doElem; let%$doLetArrow $pattern:term := __discr)
        doSeqToCode <| getDoSeqElems (getDoSeq auxDo) ++ doElems
      else
        let contSeq ← if isMutableLet doLetArrow then
          let vars ← (← getPatternVarsEx pattern).mapM fun var => `(doElem| let mut $var := $var)
          pure (vars ++ doElems.toArray)
        else
          pure doElems.toArray
        let contSeq := mkDoSeq contSeq
        let elseSeq := optElse[1]
        let auxDo ← `(do let%$doLetArrow __discr ← $doElem; match%$doLetArrow __discr with | $pattern:term => $contSeq | _ => $elseSeq)
        doSeqToCode <| getDoSeqElems (getDoSeq auxDo)
    else
      throwError "unexpected kind of `do` declaration"

  partial def doLetElseToCode (doLetElse : Syntax) (doElems : List Syntax) : M CodeBlock := do
    -- "let " >> optional "mut " >> termParser >> " := " >> termParser >> checkColGt >> " | " >> doSeq
    let pattern := doLetElse[2]
    let val     := doLetElse[4]
    let elseSeq := doLetElse[6]
    let contSeq ← if isMutableLet doLetElse then
      let vars ← (← getPatternVarsEx pattern).mapM fun var => `(doElem| let mut $var := $var)
      pure (vars ++ doElems.toArray)
    else
      pure doElems.toArray
    let contSeq := mkDoSeq contSeq
    let auxDo ← `(do let __discr := $val; match __discr with | $pattern:term => $contSeq | _ => $elseSeq)
    doSeqToCode <| getDoSeqElems (getDoSeq auxDo)

  /-- Generate `CodeBlock` for `doReassignArrow; doElems`
     `doReassignArrow` is of the form
     ```
     (doIdDecl <|> doPatDecl)
     ```
  -/
  partial def doReassignArrowToCode (doReassignArrow : Syntax) (doElems : List Syntax) : M CodeBlock := do
    let decl := doReassignArrow[0]
    if decl.getKind == ``Parser.Term.doIdDecl then
      let doElem := decl[3]
      let y      := decl[0]
      let auxDo ← `(do let r ← $doElem; $y:ident := r)
      doSeqToCode <| getDoSeqElems (getDoSeq auxDo) ++ doElems
    else if decl.getKind == ``Parser.Term.doPatDecl then
      let pattern := decl[0]
      let doElem  := decl[2]
      let optElse := decl[3]
      if optElse.isNone then withFreshMacroScope do
        let auxDo ← `(do let __discr ← $doElem; $pattern:term := __discr)
        doSeqToCode <| getDoSeqElems (getDoSeq auxDo) ++ doElems
      else
        throwError "reassignment with `|` (i.e., \"else clause\") is not currently supported"
    else
      throwError "unexpected kind of `do` reassignment"

  /-- Generate `CodeBlock` for `doIf; doElems`
     `doIf` is of the form
     ```
     "if " >> optIdent >> termParser >> " then " >> doSeq
      >> many (group (try (group (" else " >> " if ")) >> optIdent >> termParser >> " then " >> doSeq))
      >> optional (" else " >> doSeq)
     ```  -/
  partial def doIfToCode (doIf : Syntax) (doElems : List Syntax) : M CodeBlock := do
    let view := mkDoIfView doIf
    let thenBranch ← doSeqToCode (getDoSeqElems view.thenBranch)
    let elseBranch ← doSeqToCode (getDoSeqElems view.elseBranch)
    let ite ← mkIte view.ref view.optIdent view.cond thenBranch elseBranch
    concatWith ite doElems

  /-- Generate `CodeBlock` for `doUnless; doElems`
     `doUnless` is of the form
     ```
     "unless " >> termParser >> "do " >> doSeq
     ```  -/
  partial def doUnlessToCode (doUnless : Syntax) (doElems : List Syntax) : M CodeBlock := withRef doUnless do
    let cond  := doUnless[1]
    let doSeq := doUnless[3]
    let body ← doSeqToCode (getDoSeqElems doSeq)
    let unlessCode ← liftMacroM <| mkUnless cond body
    concatWith unlessCode doElems

  /-- Generate `CodeBlock` for `doFor; doElems`
     `doFor` is of the form
     ```
     def doForDecl := leading_parser termParser >> " in " >> withForbidden "do" termParser
     def doFor := leading_parser "for " >> sepBy1 doForDecl ", " >> "do " >> doSeq
     ```
  -/
  partial def doForToCode (doFor : Syntax) (doElems : List Syntax) : M CodeBlock := do
    let doForDecls := doFor[1].getSepArgs
    if doForDecls.size > 1 then
      /-
        Expand
        ```
        for x in xs, y in ys do
          body
        ```
        into
        ```
        let s := toStream ys
        for x in xs do
          match Stream.next? s with
          | none => break
          | some (y, s') =>
            s := s'
            body
        ```
      -/
      -- Extract second element
      let doForDecl := doForDecls[1]!
      unless doForDecl[0].isNone do
        throwErrorAt doForDecl[0] "the proof annotation here has not been implemented yet"
      let y  := doForDecl[1]
      let ys := doForDecl[3]
      let doForDecls := doForDecls.eraseIdx 1
      let body := doFor[3]
      withFreshMacroScope do
        /- Recall that `@` (explicit) disables `coeAtOutParam`.
           We used `@` at `Stream` functions to make sure `resultIsOutParamSupport` is not used. -/
        let toStreamApp ← withRef ys `(@toStream _ _ _ $ys)
        let auxDo ←
          `(do let mut s := $toStreamApp:term
               for $doForDecls:doForDecl,* do
                 match @Stream.next? _ _ _ s with
                 | none => break
                 | some ($y, s') =>
                   s := s'
                   do $body)
        doSeqToCode (getDoSeqElems (getDoSeq auxDo) ++ doElems)
    else withRef doFor do
      let h?        := if doForDecls[0]![0].isNone then none else some doForDecls[0]![0][0]
      let x         := doForDecls[0]![1]
      withRef x <| checkNotShadowingMutable (← getPatternVarsEx x)
      let xs        := doForDecls[0]![3]
      let forElems  := getDoSeqElems doFor[3]
      let forInBodyCodeBlock ← withFor (doSeqToCode forElems)
      let ⟨uvars, forInBody⟩ ← mkForInBody x forInBodyCodeBlock
      let ctx ← read
      -- semantic no-op that replaces the `uvars`' position information (which all point inside the loop)
      -- with that of the respective mutable declarations outside the loop, which allows the language
      -- server to identify them as conceptually identical variables
      let uvars := uvars.map fun v => ctx.mutableVars.findD v.getId v
      let uvarsTuple ← liftMacroM do mkTuple uvars
      if hasReturn forInBodyCodeBlock.code then
        let forInBody ← liftMacroM <| destructTuple uvars (← `(r)) forInBody
        let optType ← `(Option $((← read).returnType))
        let forInTerm ← if let some h := h? then
          annotate doFor
            (← `(for_in'% $(xs) (MProd.mk (none : $optType) $uvarsTuple) fun $x $h (r : MProd $optType _) => let r := r.2; $forInBody))
        else
          annotate doFor
            (← `(for_in% $(xs) (MProd.mk (none : $optType) $uvarsTuple) fun $x (r : MProd $optType _) => let r := r.2; $forInBody))
        let auxDo ← `(do let r ← $forInTerm:term;
                         $uvarsTuple:term := r.2;
                         match r.1 with
                         | none => Pure.pure (ensure_expected_type% "type mismatch, `for`" PUnit.unit)
                         | some a => return ensure_expected_type% "type mismatch, `for`" a)
        doSeqToCode (getDoSeqElems (getDoSeq auxDo) ++ doElems)
      else
        let forInBody ← liftMacroM <| destructTuple uvars (← `(r)) forInBody
        let forInTerm ← if let some h := h? then
          annotate doFor (← `(for_in'% $(xs) $uvarsTuple fun $x $h r => $forInBody))
        else
          annotate doFor (← `(for_in% $(xs) $uvarsTuple fun $x r => $forInBody))
        if doElems.isEmpty then
          let auxDo ← `(do let r ← $forInTerm:term;
                           $uvarsTuple:term := r;
                           Pure.pure (ensure_expected_type% "type mismatch, `for`" PUnit.unit))
          doSeqToCode <| getDoSeqElems (getDoSeq auxDo)
        else
          let auxDo ← `(do let r ← $forInTerm:term; $uvarsTuple:term := r)
          doSeqToCode <| getDoSeqElems (getDoSeq auxDo) ++ doElems

  /-- Generate `CodeBlock` for `doMatch; doElems` -/
  partial def doMatchToCode (doMatch : Syntax) (doElems: List Syntax) : M CodeBlock := do
    let ref       := doMatch
    let genParam  := doMatch[1]
    let optMotive := doMatch[2]
    let discrs    := doMatch[3]
    let matchAlts := doMatch[5][0].getArgs -- Array of `doMatchAlt`
    let matchAlts ← matchAlts.foldlM (init := #[]) fun result matchAlt => return result ++ (← liftMacroM <| expandMatchAlt matchAlt)
    let alts ←  matchAlts.mapM fun matchAlt => do
      let patterns := matchAlt[1][0]
      let vars ← getPatternsVarsEx patterns.getSepArgs
      withRef patterns <| checkNotShadowingMutable vars
      let rhs  := matchAlt[3]
      let rhs ← doSeqToCode (getDoSeqElems rhs)
      pure { ref := matchAlt, vars := vars, patterns := patterns, rhs := rhs : Alt CodeBlock }
    let matchCode ← mkMatch ref genParam discrs optMotive alts
    concatWith matchCode doElems

  /--
    Generate `CodeBlock` for `doTry; doElems`
    ```
    def doTry := leading_parser "try " >> doSeq >> many (doCatch <|> doCatchMatch) >> optional doFinally
    def doCatch      := leading_parser "catch " >> binderIdent >> optional (":" >> termParser) >> darrow >> doSeq
    def doCatchMatch := leading_parser "catch " >> doMatchAlts
    def doFinally    := leading_parser "finally " >> doSeq
    ```
  -/
  partial def doTryToCode (doTry : Syntax) (doElems: List Syntax) : M CodeBlock := do
    let tryCode ← doSeqToCode (getDoSeqElems doTry[1])
    let optFinally := doTry[3]
    let catches ← doTry[2].getArgs.mapM fun catchStx : Syntax => do
      if catchStx.getKind == ``Parser.Term.doCatch then
        let x       := catchStx[1]
        if x.isIdent then
          withRef x <| checkNotShadowingMutable #[x]
        let optType := catchStx[2]
        let c ← doSeqToCode (getDoSeqElems catchStx[4])
        return { x := x, optType := optType, codeBlock := c : Catch }
      else if catchStx.getKind == ``Parser.Term.doCatchMatch then
        let matchAlts := catchStx[1]
        let x ← `(ex)
        let auxDo ← `(do match ex with $matchAlts)
        let c ← doSeqToCode (getDoSeqElems (getDoSeq auxDo))
        return { x := x, codeBlock := c, optType := mkNullNode : Catch }
      else
        throwError "unexpected kind of `catch`"
    let finallyCode? ← if optFinally.isNone then pure none else some <$> doSeqToCode (getDoSeqElems optFinally[0][1])
    if catches.isEmpty && finallyCode?.isNone then
      throwError "invalid `try`, it must have a `catch` or `finally`"
    let ctx ← read
    let ws    := getTryCatchUpdatedVars tryCode catches finallyCode?
    let uvars := varSetToArray ws
    let a     := tryCatchPred tryCode catches finallyCode? hasTerminalAction
    let r     := tryCatchPred tryCode catches finallyCode? hasReturn
    let bc    := tryCatchPred tryCode catches finallyCode? hasBreakContinue
    let toTerm (codeBlock : CodeBlock) : M Syntax := do
      let codeBlock ← liftM $ extendUpdatedVars codeBlock ws
      liftMacroM <| ToTerm.mkNestedTerm codeBlock.code ctx.m ctx.returnType uvars a r bc
    let term ← toTerm tryCode
    let term ← catches.foldlM (init := term) fun term «catch» => do
      let catchTerm ← toTerm «catch».codeBlock
      if catch.optType.isNone then
        annotate doTry (← ``(MonadExcept.tryCatch $term (fun $(«catch».x):ident => $catchTerm)))
      else
        let type := «catch».optType[1]
        annotate doTry (← ``(tryCatchThe $type $term (fun $(«catch».x):ident => $catchTerm)))
    let term ← match finallyCode? with
      | none             => pure term
      | some finallyCode => withRef optFinally do
        unless finallyCode.uvars.isEmpty do
          throwError "`finally` currently does not support reassignments"
        if hasBreakContinueReturn finallyCode.code then
          throwError "`finally` currently does `return`, `break`, nor `continue`"
        let finallyTerm ← liftMacroM <| ToTerm.run finallyCode.code ctx.m ctx.returnType {} ToTerm.Kind.regular
        annotate doTry (← ``(tryFinally $term $finallyTerm))
    let doElemsNew ← liftMacroM <| ToTerm.matchNestedTermResult term uvars a r bc
    doSeqToCode (doElemsNew ++ doElems)

  partial def doSeqToCode : List Syntax → M CodeBlock
    | [] => do liftMacroM mkPureUnitAction
    | doElem::doElems => withIncRecDepth <| withRef doElem do
      checkSystem "`do`-expander"
      match (← liftMacroM <| expandMacro? doElem) with
      | some doElem => doSeqToCode (doElem::doElems)
      | none =>
      match (← liftMacroM <| expandDoIf? doElem) with
      | some doElem => doSeqToCode (doElem::doElems)
      | none =>
        let (liftedDoElems, doElem) ← expandLiftMethod doElem
        if !liftedDoElems.isEmpty then
          doSeqToCode (liftedDoElems ++ [doElem] ++ doElems)
        else
          let ref := doElem
          let k := doElem.getKind
          if k == ``Parser.Term.doLet then
            let vars ← getDoLetVars doElem
            checkNotShadowingMutable vars
            mkVarDeclCore vars doElem <$> withNewMutableVars vars (isMutableLet doElem) (doSeqToCode doElems)
          else if k == ``Parser.Term.doHave then
            let vars ← getDoHaveVars doElem
            checkNotShadowingMutable vars
            mkVarDeclCore vars doElem <$> (doSeqToCode doElems)
          else if k == ``Parser.Term.doLetRec then
            let vars ← getDoLetRecVars doElem
            checkNotShadowingMutable vars
            mkVarDeclCore vars doElem <$> (doSeqToCode doElems)
          else if k == ``Parser.Term.doReassign then
            let vars ← getDoReassignVars doElem
            checkReassignable vars
            let k ← doSeqToCode doElems
            mkReassignCore vars doElem k
          else if k == ``Parser.Term.doLetArrow then
            doLetArrowToCode doElem doElems
          else if k == ``Parser.Term.doLetElse then
            doLetElseToCode doElem doElems
          else if k == ``Parser.Term.doReassignArrow then
            doReassignArrowToCode doElem doElems
          else if k == ``Parser.Term.doIf then
            doIfToCode doElem doElems
          else if k == ``Parser.Term.doUnless then
            doUnlessToCode doElem doElems
          else if k == ``Parser.Term.doFor then withFreshMacroScope do
            doForToCode doElem doElems
          else if k == ``Parser.Term.doMatch then
            doMatchToCode doElem doElems
          else if k == ``Parser.Term.doTry then
            doTryToCode doElem doElems
          else if k == ``Parser.Term.doBreak then
            ensureInsideFor
            ensureEOS doElems
            return mkBreak ref
          else if k == ``Parser.Term.doContinue then
            ensureInsideFor
            ensureEOS doElems
            return mkContinue ref
          else if k == ``Parser.Term.doReturn then
            doReturnToCode doElem doElems
          else if k == ``Parser.Term.doDbgTrace then
            return mkSeq doElem (← doSeqToCode doElems)
          else if k == ``Parser.Term.doAssert then
            return mkSeq doElem (← doSeqToCode doElems)
          else if k == ``Parser.Term.doNested then
            let nestedDoSeq := doElem[1]
            doSeqToCode (getDoSeqElems nestedDoSeq ++ doElems)
          else if k == ``Parser.Term.doExpr then
            let term := doElem[0]
            if doElems.isEmpty then
              return mkTerminalAction term
            else
              return mkSeq term (← doSeqToCode doElems)
          else
            throwError "unexpected do-element of kind {doElem.getKind}:\n{doElem}"
end

def run (doStx : Syntax) (m : Syntax) (returnType : Syntax) : TermElabM CodeBlock :=
  (doSeqToCode <| getDoSeqElems <| getDoSeq doStx).run { ref := doStx, m, returnType }

end ToCodeBlock

@[builtin_term_elab «do»] def elabDo : TermElab := fun stx expectedType? => do
  tryPostponeIfNoneOrMVar expectedType?
  let bindInfo ← extractBind expectedType?
  let m ← Term.exprToSyntax bindInfo.m
  let returnType ← Term.exprToSyntax bindInfo.returnType
  let codeBlock ← ToCodeBlock.run stx m returnType
  let stxNew ← liftMacroM <| ToTerm.run codeBlock.code m returnType
  trace[Elab.do] stxNew
  withMacroExpansion stx stxNew <| elabTermEnsuringType stxNew bindInfo.expectedType

end Do

builtin_initialize registerTraceClass `Elab.do

private def toDoElem (newKind : SyntaxNodeKind) : Macro := fun stx => do
  let stx := stx.setKind newKind
  withRef stx `(do $stx:doElem)

@[builtin_macro Lean.Parser.Term.termFor]
def expandTermFor : Macro := toDoElem ``Parser.Term.doFor

@[builtin_macro Lean.Parser.Term.termTry]
def expandTermTry : Macro := toDoElem ``Parser.Term.doTry

@[builtin_macro Lean.Parser.Term.termUnless]
def expandTermUnless : Macro := toDoElem ``Parser.Term.doUnless

@[builtin_macro Lean.Parser.Term.termReturn]
def expandTermReturn : Macro := toDoElem ``Parser.Term.doReturn

end Lean.Elab.Term
