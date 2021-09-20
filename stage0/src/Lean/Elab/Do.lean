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

private def getDoSeqElems (doSeq : Syntax) : List Syntax :=
  if doSeq.getKind == ``Lean.Parser.Term.doSeqBracketed then
    doSeq[1].getArgs.toList.map fun arg => arg[0]
  else if doSeq.getKind == ``Lean.Parser.Term.doSeqIndent then
    doSeq[0].getArgs.toList.map fun arg => arg[0]
  else
    []

private def getDoSeq (doStx : Syntax) : Syntax :=
  doStx[1]

@[builtinTermElab liftMethod] def elabLiftMethod : TermElab := fun stx _ =>
  throwErrorAt stx "invalid use of `(<- ...)`, must be nested inside a 'do' expression"

/-- Return true if we should not lift `(<- ...)` actions nested in the syntax nodes with the given kind. -/
private def liftMethodDelimiter (k : SyntaxNodeKind) : Bool :=
  k == ``Lean.Parser.Term.do ||
  k == ``Lean.Parser.Term.doSeqIndent ||
  k == ``Lean.Parser.Term.doSeqBracketed ||
  k == ``Lean.Parser.Term.termReturn ||
  k == ``Lean.Parser.Term.termUnless ||
  k == ``Lean.Parser.Term.termTry ||
  k == ``Lean.Parser.Term.termFor

/-- Given `stx` which is a `letPatDecl`, `letEqnsDecl`, or `letIdDecl`, return true if it has binders. -/
private def letDeclArgHasBinders (letDeclArg : Syntax) : Bool :=
  let k := letDeclArg.getKind
  if k == ``Lean.Parser.Term.letPatDecl then
    false
  else if k == ``Lean.Parser.Term.letEqnsDecl then
    true
  else if k == ``Lean.Parser.Term.letIdDecl then
    -- letIdLhs := ident >> checkWsBefore "expected space before binders" >> many (ppSpace >> (simpleBinderWithoutType <|> bracketedBinder)) >> optType
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
  if k == ``Lean.Parser.Term.fun || k == ``Lean.Parser.Term.matchAlts ||
     k == ``Lean.Parser.Term.doLetRec || k == ``Lean.Parser.Term.letrec  then
     -- It is never ok to lift over this kind of binder
    true
  -- The following kinds of `let`-expressions require extra checks to decide whether they contain binders or not
  else if k == ``Lean.Parser.Term.let then
    letDeclHasBinders stx[1]
  else if k == ``Lean.Parser.Term.doLet then
    letDeclHasBinders stx[2]
  else if k == ``Lean.Parser.Term.doLetArrow then
    letDeclArgHasBinders stx[2]
  else
    false

private partial def hasLiftMethod : Syntax → Bool
  | Syntax.node k args =>
    if liftMethodDelimiter k then false
    -- NOTE: We don't check for lifts in quotations here, which doesn't break anything but merely makes this rare case a
    -- bit slower
    else if k == ``Lean.Parser.Term.liftMethod then true
    else args.any hasLiftMethod
  | _ => false

structure ExtractMonadResult where
  m            : Expr
  α            : Expr
  hasBindInst  : Expr
  expectedType : Expr
  isPure       : Bool -- `true` when it is a pure `do` block. That is, Lean implicitly inserted the `Id` Monad.

private def mkIdBindFor (type : Expr) : TermElabM ExtractMonadResult := do
  let u ← getDecLevel type
  let id        := Lean.mkConst ``Id [u]
  let idBindVal := Lean.mkConst ``Id.hasBind [u]
  pure { m := id, hasBindInst := idBindVal, α := type, expectedType := mkApp id type, isPure := true }

private partial def extractBind (expectedType? : Option Expr) : TermElabM ExtractMonadResult := do
  match expectedType? with
  | none => throwError "invalid 'do' notation, expected type is not available"
  | some expectedType =>
    let extractStep? (type : Expr) : MetaM (Option ExtractMonadResult) := do
      match type with
      | Expr.app m α _ =>
        try
          let bindInstType ← mkAppM ``Bind #[m]
          let bindInstVal  ← Meta.synthInstance bindInstType
          return some { m := m, hasBindInst := bindInstVal, α := α, expectedType := expectedType, isPure := false }
        catch _ =>
          return none
      | _ =>
        return none
    let rec extract? (type : Expr) : MetaM (Option ExtractMonadResult) := do
      match (← extractStep? type) with
      | some r => return r
      | none =>
        let typeNew ← whnfCore type
        if typeNew != type then
          extract? typeNew
        else
          if typeNew.getAppFn.isMVar then throwError "invalid 'do' notation, expected type is not available"
          match (← unfoldDefinition? typeNew) with
          | some typeNew => extract? typeNew
          | none => return none
    match (← extract? expectedType) with
    | some r => return r
    | none   => mkIdBindFor expectedType

namespace Do

/- A `doMatch` alternative. `vars` is the array of variables declared by `patterns`. -/
structure Alt (σ : Type) where
  ref : Syntax
  vars : Array Name
  patterns : Syntax
  rhs : σ
  deriving Inhabited

/-
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
  | decl         (xs : Array Name) (doElem : Syntax) (k : Code)
  | reassign     (xs : Array Name) (doElem : Syntax) (k : Code)
  /- The Boolean value in `params` indicates whether we should use `(x : typeof! x)` when generating term Syntax or not -/
  | joinpoint    (name : Name) (params : Array (Name × Bool)) (body : Code) (k : Code)
  | seq          (action : Syntax) (k : Code)
  | action       (action : Syntax)
  | «break»      (ref : Syntax)
  | «continue»   (ref : Syntax)
  | «return»     (ref : Syntax) (val : Syntax)
  /- Recall that an if-then-else may declare a variable using `optIdent` for the branches `thenBranch` and `elseBranch`. We store the variable name at `var?`. -/
  | ite          (ref : Syntax) (h? : Option Name) (optIdent : Syntax) (cond : Syntax) (thenBranch : Code) (elseBranch : Code)
  | «match»      (ref : Syntax) (gen : Syntax) (discrs : Syntax) (optType : Syntax) (alts : Array (Alt Code))
  | jmp          (ref : Syntax) (jpName : Name) (args : Array Syntax)
  deriving Inhabited

/- A code block, and the collection of variables updated by it. -/
structure CodeBlock where
  code  : Code
  uvars : NameSet := {} -- set of variables updated by `code`

private def nameSetToArray (s : NameSet) : Array Name :=
  s.fold (fun (xs : Array Name) x => xs.push x) #[]

private def varsToMessageData (vars : Array Name) : MessageData :=
  MessageData.joinSep (vars.toList.map fun n => MessageData.ofName (n.simpMacroScopes)) " "

partial def CodeBlocl.toMessageData (codeBlock : CodeBlock) : MessageData :=
  let us := MessageData.ofList $ (nameSetToArray codeBlock.uvars).toList.map MessageData.ofName
  let rec loop : Code → MessageData
    | Code.decl xs _ k            => m!"let {varsToMessageData xs} := ...\n{loop k}"
    | Code.reassign xs _ k        => m!"{varsToMessageData xs} := ...\n{loop k}"
    | Code.joinpoint n ps body k  => m!"let {n.simpMacroScopes} {varsToMessageData (ps.map Prod.fst)} := {indentD (loop body)}\n{loop k}"
    | Code.seq e k                => m!"{e}\n{loop k}"
    | Code.action e               => e
    | Code.ite _ _ _ c t e        => m!"if {c} then {indentD (loop t)}\nelse{loop e}"
    | Code.jmp _ j xs             => m!"jmp {j.simpMacroScopes} {xs.toList}"
    | Code.«break» _              => m!"break {us}"
    | Code.«continue» _           => m!"continue {us}"
    | Code.«return» _ v           => m!"return {v} {us}"
    | Code.«match» _ _ ds t alts  =>
      m!"match {ds} with"
      ++ alts.foldl (init := m!"") fun acc alt => acc ++ m!"\n| {alt.patterns} => {loop alt.rhs}"
  loop codeBlock.code

/- Return true if the give code contains an exit point that satisfies `p` -/
partial def hasExitPointPred (c : Code) (p : Code → Bool) : Bool :=
  let rec loop : Code → Bool
    | Code.decl _ _ k           => loop k
    | Code.reassign _ _ k       => loop k
    | Code.joinpoint _ _ b k    => loop b || loop k
    | Code.seq _ k              => loop k
    | Code.ite _ _ _ _ t e      => loop t || loop e
    | Code.«match» _ _ _ _ alts => alts.any (loop ·.rhs)
    | Code.jmp _ _ _            => false
    | c                         => p c
  loop c

def hasExitPoint (c : Code) : Bool :=
  hasExitPointPred c fun c => true

def hasReturn (c : Code) : Bool :=
  hasExitPointPred c fun
    | Code.«return» _ _ => true
    | _ => false

def hasTerminalAction (c : Code) : Bool :=
  hasExitPointPred c fun
    | Code.«action» _ => true
    | _ => false

def hasBreakContinue (c : Code) : Bool :=
  hasExitPointPred c fun
    | Code.«break» _    => true
    | Code.«continue» _ => true
    | _ => false

def hasBreakContinueReturn (c : Code) : Bool :=
  hasExitPointPred c fun
    | Code.«break» _    => true
    | Code.«continue» _ => true
    | Code.«return» _ _ => true
    | _ => false

def mkAuxDeclFor {m} [Monad m] [MonadQuotation m] (e : Syntax) (mkCont : Syntax → m Code) : m Code := withRef e <| withFreshMacroScope do
  let y ← `(y)
  let yName := y.getId
  let doElem ← `(doElem| let y ← $e:term)
  -- Add elaboration hint for producing sane error message
  let y ← `(ensureExpectedType% "type mismatch, result value" $y)
  let k ← mkCont y
  pure $ Code.decl #[yName] doElem k

/- Convert `action _ e` instructions in `c` into `let y ← e; jmp _ jp (xs y)`. -/
partial def convertTerminalActionIntoJmp (code : Code) (jp : Name) (xs : Array Name) : MacroM Code :=
  let rec loop : Code → MacroM Code
    | Code.decl xs stx k           => do Code.decl xs stx (← loop k)
    | Code.reassign xs stx k       => do Code.reassign xs stx (← loop k)
    | Code.joinpoint n ps b k      => do Code.joinpoint n ps (← loop b) (← loop k)
    | Code.seq e k                 => do Code.seq e (← loop k)
    | Code.ite ref x? h c t e      => do Code.ite ref x? h c (← loop t) (← loop e)
    | Code.«match» ref g ds t alts => do Code.«match» ref g ds t (← alts.mapM fun alt => do pure { alt with rhs := (← loop alt.rhs) })
    | Code.action e                => mkAuxDeclFor e fun y =>
      let ref := e
      -- We jump to `jp` with xs **and** y
      let jmpArgs := xs.map $ mkIdentFrom ref
      let jmpArgs := jmpArgs.push y
      pure $ Code.jmp ref jp jmpArgs
    | c                            => pure c
  loop code

structure JPDecl where
  name : Name
  params : Array (Name × Bool)
  body : Code

def attachJP (jpDecl : JPDecl) (k : Code) : Code :=
  Code.joinpoint jpDecl.name jpDecl.params jpDecl.body k

def attachJPs (jpDecls : Array JPDecl) (k : Code) : Code :=
  jpDecls.foldr attachJP k

def mkFreshJP (ps : Array (Name × Bool)) (body : Code) : TermElabM JPDecl := do
  let ps ←
    if ps.isEmpty then
      let y ← mkFreshUserName `y
      pure #[(y, false)]
    else
      pure ps
  -- Remark: the compiler frontend implemented in C++ currently detects jointpoints created by
  -- the "do" notation by testing the name. See hack at method `visit_let` at `lcnf.cpp`
  -- We will remove this hack when we re-implement the compiler frontend in Lean.
  let name ← mkFreshUserName `_do_jp
  pure { name := name, params := ps, body := body }

def mkFreshJP' (xs : Array Name) (body : Code) : TermElabM JPDecl :=
  mkFreshJP (xs.map fun x => (x, true)) body

def addFreshJP (ps : Array (Name × Bool)) (body : Code) : StateRefT (Array JPDecl) TermElabM Name := do
  let jp ← mkFreshJP ps body
  modify fun (jps : Array JPDecl) => jps.push jp
  pure jp.name

def insertVars (rs : NameSet) (xs : Array Name) : NameSet :=
  xs.foldl (·.insert ·) rs

def eraseVars (rs : NameSet) (xs : Array Name) : NameSet :=
  xs.foldl (·.erase ·) rs

def eraseOptVar (rs : NameSet) (x? : Option Name) : NameSet :=
  match x? with
  | none   => rs
  | some x => rs.insert x

/- Create a new jointpoint for `c`, and jump to it with the variables `rs` -/
def mkSimpleJmp (ref : Syntax) (rs : NameSet) (c : Code) : StateRefT (Array JPDecl) TermElabM Code := do
  let xs := nameSetToArray rs
  let jp ← addFreshJP (xs.map fun x => (x, true)) c
  if xs.isEmpty then
    let unit ← ``(Unit.unit)
    return Code.jmp ref jp #[unit]
  else
    return Code.jmp ref jp (xs.map $ mkIdentFrom ref)

/- Create a new joinpoint that takes `rs` and `val` as arguments. `val` must be syntax representing a pure value.
   The body of the joinpoint is created using `mkJPBody yFresh`, where `yFresh`
   is a fresh variable created by this method. -/
def mkJmp (ref : Syntax) (rs : NameSet) (val : Syntax) (mkJPBody : Syntax → MacroM Code) : StateRefT (Array JPDecl) TermElabM Code := do
  let xs := nameSetToArray rs
  let args := xs.map $ mkIdentFrom ref
  let args := args.push val
  let yFresh ← mkFreshUserName `y
  let ps := xs.map fun x => (x, true)
  let ps := ps.push (yFresh, false)
  let jpBody ← liftMacroM $ mkJPBody (mkIdentFrom ref yFresh)
  let jp ← addFreshJP ps jpBody
  pure $ Code.jmp ref jp args

/- `pullExitPointsAux rs c` auxiliary method for `pullExitPoints`, `rs` is the set of update variable in the current path.  -/
partial def pullExitPointsAux : NameSet → Code → StateRefT (Array JPDecl) TermElabM Code
  | rs, Code.decl xs stx k           => do Code.decl xs stx (← pullExitPointsAux (eraseVars rs xs) k)
  | rs, Code.reassign xs stx k       => do Code.reassign xs stx (← pullExitPointsAux (insertVars rs xs) k)
  | rs, Code.joinpoint j ps b k      => do Code.joinpoint j ps (← pullExitPointsAux rs b) (← pullExitPointsAux rs k)
  | rs, Code.seq e k                 => do Code.seq e (← pullExitPointsAux rs k)
  | rs, Code.ite ref x? o c t e      => do Code.ite ref x? o c (← pullExitPointsAux (eraseOptVar rs x?) t) (← pullExitPointsAux (eraseOptVar rs x?) e)
  | rs, Code.«match» ref g ds t alts => do
    Code.«match» ref g ds t (← alts.mapM fun alt => do pure { alt with rhs := (← pullExitPointsAux (eraseVars rs alt.vars) alt.rhs) })
  | rs, c@(Code.jmp _ _ _)           => pure c
  | rs, Code.«break» ref             => mkSimpleJmp ref rs (Code.«break» ref)
  | rs, Code.«continue» ref          => mkSimpleJmp ref rs (Code.«continue» ref)
  | rs, Code.«return» ref val        => mkJmp ref rs val (fun y => pure $ Code.«return» ref y)
  | rs, Code.action e                =>
    -- We use `mkAuxDeclFor` because `e` is not pure.
    mkAuxDeclFor e fun y =>
      let ref := e
      mkJmp ref rs y (fun yFresh => do pure $ Code.action (← ``(Pure.pure $yFresh)))

/-
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
    pure $ attachJPs jpDecls c
  else
    pure c

partial def extendUpdatedVarsAux (c : Code) (ws : NameSet) : TermElabM Code :=
  let rec update : Code → TermElabM Code
    | Code.joinpoint j ps b k          => do Code.joinpoint j ps (← update b) (← update k)
    | Code.seq e k                     => do Code.seq e (← update k)
    | c@(Code.«match» ref g ds t alts) => do
      if alts.any fun alt => alt.vars.any fun x => ws.contains x then
        -- If a pattern variable is shadowing a variable in ws, we `pullExitPoints`
        pullExitPoints c
      else
        Code.«match» ref g ds t (← alts.mapM fun alt => do pure { alt with rhs := (← update alt.rhs) })
    | Code.ite ref none o c t e => do Code.ite ref none o c (← update t) (← update e)
    | c@(Code.ite ref (some h) o cond t e) => do
      if ws.contains h then
        -- if the `h` at `if h:c then t else e` shadows a variable in `ws`, we `pullExitPoints`
        pullExitPoints c
      else
        Code.ite ref (some h) o cond (← update t) (← update e)
    | Code.reassign xs stx k => do Code.reassign xs stx (← update k)
    | c@(Code.decl xs stx k) => do
      if xs.any fun x => ws.contains x then
        -- One the declared variables is shadowing a variable in `ws`
        pullExitPoints c
      else
        Code.decl xs stx (← update k)
    | c => pure c
  update c

/-
Extend the set of updated variables. It assumes `ws` is a super set of `c.uvars`.
We **cannot** simply update the field `c.uvars`, because `c` may have shadowed some variable in `ws`.
See discussion at `pullExitPoints`.
-/
partial def extendUpdatedVars (c : CodeBlock) (ws : NameSet) : TermElabM CodeBlock := do
  if ws.any fun x => !c.uvars.contains x then
    -- `ws` contains a variable that is not in `c.uvars`, but in `c.dvars` (i.e., it has been shadowed)
    pure { code := (← extendUpdatedVarsAux c.code ws), uvars := ws }
  else
    pure { c with uvars := ws }

private def union (s₁ s₂ : NameSet) : NameSet :=
  s₁.fold (·.insert ·) s₂

/-
Given two code blocks `c₁` and `c₂`, make sure they have the same set of updated variables.
Let `ws` the union of the updated variables in `c₁‵ and ‵c₂`.
We use `extendUpdatedVars c₁ ws` and `extendUpdatedVars c₂ ws`
-/
def homogenize (c₁ c₂ : CodeBlock) : TermElabM (CodeBlock × CodeBlock) := do
  let ws := union c₁.uvars c₂.uvars
  let c₁ ← extendUpdatedVars c₁ ws
  let c₂ ← extendUpdatedVars c₂ ws
  pure (c₁, c₂)

/-
Extending code blocks with variable declarations: `let x : t := v` and `let x : t ← v`.
We remove `x` from the collection of updated varibles.
Remark: `stx` is the syntax for the declaration (e.g., `letDecl`), and `xs` are the variables
declared by it. It is an array because we have let-declarations that declare multiple variables.
Example: `let (x, y) := t`
-/
def mkVarDeclCore (xs : Array Name) (stx : Syntax) (c : CodeBlock) : CodeBlock := {
  code := Code.decl xs stx c.code,
  uvars := eraseVars c.uvars xs
}

/-
Extending code blocks with reassignments: `x : t := v` and `x : t ← v`.
Remark: `stx` is the syntax for the declaration (e.g., `letDecl`), and `xs` are the variables
declared by it. It is an array because we have let-declarations that declare multiple variables.
Example: `(x, y) ← t`
-/
def mkReassignCore (xs : Array Name) (stx : Syntax) (c : CodeBlock) : TermElabM CodeBlock := do
  let us := c.uvars
  let ws := insertVars us xs
  -- If `xs` contains a new updated variable, then we must use `extendUpdatedVars`.
  -- See discussion at `pullExitPoints`
  let code ← if xs.any fun x => !us.contains x then extendUpdatedVarsAux c.code ws else pure c.code
  pure { code := Code.reassign xs stx code, uvars := ws }

def mkSeq (action : Syntax) (c : CodeBlock) : CodeBlock :=
  { c with code := Code.seq action c.code }

def mkTerminalAction (action : Syntax) : CodeBlock :=
  { code := Code.action action }

def mkReturn (ref : Syntax) (val : Syntax) : CodeBlock :=
  { code := Code.«return» ref val }

def mkBreak (ref : Syntax) : CodeBlock :=
  { code := Code.«break» ref }

def mkContinue (ref : Syntax) : CodeBlock :=
  { code := Code.«continue» ref }

def mkIte (ref : Syntax) (optIdent : Syntax) (cond : Syntax) (thenBranch : CodeBlock) (elseBranch : CodeBlock) : TermElabM CodeBlock := do
  let x? := if optIdent.isNone then none else some optIdent[0].getId
  let (thenBranch, elseBranch) ← homogenize thenBranch elseBranch
  pure {
    code  := Code.ite ref x? optIdent cond thenBranch.code elseBranch.code,
    uvars := thenBranch.uvars,
  }

private def mkUnit : MacroM Syntax :=
  ``((⟨⟩ : PUnit))

private def mkPureUnit : MacroM Syntax :=
  ``(pure PUnit.unit)

def mkPureUnitAction : MacroM CodeBlock := do
  mkTerminalAction (← mkPureUnit)

def mkUnless (cond : Syntax) (c : CodeBlock) : MacroM CodeBlock := do
  let thenBranch ← mkPureUnitAction
  pure { c with code := Code.ite (← getRef) none mkNullNode cond thenBranch.code c.code }

def mkMatch (ref : Syntax) (genParam : Syntax) (discrs : Syntax) (optType : Syntax) (alts : Array (Alt CodeBlock)) : TermElabM CodeBlock := do
  -- nary version of homogenize
  let ws := alts.foldl (union · ·.rhs.uvars) {}
  let alts ← alts.mapM fun alt => do
    let rhs ← extendUpdatedVars alt.rhs ws
    pure { ref := alt.ref, vars := alt.vars, patterns := alt.patterns, rhs := rhs.code : Alt Code }
  pure { code := Code.«match» ref genParam discrs optType alts, uvars := ws }

/- Return a code block that executes `terminal` and then `k` with the value produced by `terminal`.
   This method assumes `terminal` is a terminal -/
def concat (terminal : CodeBlock) (kRef : Syntax) (y? : Option Name) (k : CodeBlock) : TermElabM CodeBlock := do
  unless hasTerminalAction terminal.code do
    throwErrorAt kRef "'do' element is unreachable"
  let (terminal, k) ← homogenize terminal k
  let xs := nameSetToArray k.uvars
  let y ← match y? with | some y => pure y | none => mkFreshUserName `y
  let ps := xs.map fun x => (x, true)
  let ps := ps.push (y, false)
  let jpDecl ← mkFreshJP ps k.code
  let jp := jpDecl.name
  let terminal ← liftMacroM $ convertTerminalActionIntoJmp terminal.code jp xs
  pure { code  := attachJP jpDecl terminal, uvars := k.uvars }

def getLetIdDeclVar (letIdDecl : Syntax) : Name :=
  letIdDecl[0].getId

-- support both regular and syntax match
def getPatternVarsEx (pattern : Syntax) : TermElabM (Array Name) :=
  getPatternVarNames <$> getPatternVars pattern <|>
  Array.map Syntax.getId <$> Quotation.getPatternVars pattern

def getPatternsVarsEx (patterns : Array Syntax) : TermElabM (Array Name) :=
  getPatternVarNames <$> getPatternsVars patterns <|>
  Array.map Syntax.getId <$> Quotation.getPatternsVars patterns

def getLetPatDeclVars (letPatDecl : Syntax) : TermElabM (Array Name) := do
  let pattern := letPatDecl[0]
  getPatternVarsEx pattern

def getLetEqnsDeclVar (letEqnsDecl : Syntax) : Name :=
  letEqnsDecl[0].getId

def getLetDeclVars (letDecl : Syntax) : TermElabM (Array Name) := do
  let arg := letDecl[0]
  if arg.getKind == ``Lean.Parser.Term.letIdDecl then
    pure #[getLetIdDeclVar arg]
  else if arg.getKind == ``Lean.Parser.Term.letPatDecl then
    getLetPatDeclVars arg
  else if arg.getKind == ``Lean.Parser.Term.letEqnsDecl then
    pure #[getLetEqnsDeclVar arg]
  else
    throwError "unexpected kind of let declaration"

def getDoLetVars (doLet : Syntax) : TermElabM (Array Name) :=
  -- leading_parser "let " >> optional "mut " >> letDecl
  getLetDeclVars doLet[2]

def getDoHaveVar (doHave : Syntax) : Name :=
  /-
    `leading_parser "have " >> Term.haveDecl`
    where
    ```
    haveDecl := leading_parser optIdent >> termParser >> (haveAssign <|> fromTerm <|> byTactic)
    optIdent := optional (try (ident >> " : "))

    ```
  -/
  let optIdent := doHave[1][0]
  if optIdent.isNone then
    `this
  else
    optIdent[0].getId

def getDoLetRecVars (doLetRec : Syntax) : TermElabM (Array Name) := do
  -- letRecDecls is an array of `(group (optional attributes >> letDecl))`
  let letRecDecls := doLetRec[1][0].getSepArgs
  let letDecls := letRecDecls.map fun p => p[2]
  let mut allVars := #[]
  for letDecl in letDecls do
    let vars ← getLetDeclVars letDecl
    allVars := allVars ++ vars
  pure allVars

-- ident >> optType >> leftArrow >> termParser
def getDoIdDeclVar (doIdDecl : Syntax) : Name :=
  doIdDecl[0].getId

-- termParser >> leftArrow >> termParser >> optional (" | " >> termParser)
def getDoPatDeclVars (doPatDecl : Syntax) : TermElabM (Array Name) := do
  let pattern := doPatDecl[0]
  getPatternVarsEx pattern

-- leading_parser "let " >> optional "mut " >> (doIdDecl <|> doPatDecl)
def getDoLetArrowVars (doLetArrow : Syntax) : TermElabM (Array Name) := do
  let decl := doLetArrow[2]
  if decl.getKind == ``Lean.Parser.Term.doIdDecl then
    pure #[getDoIdDeclVar decl]
  else if decl.getKind == ``Lean.Parser.Term.doPatDecl then
    getDoPatDeclVars decl
  else
    throwError "unexpected kind of 'do' declaration"

def getDoReassignVars (doReassign : Syntax) : TermElabM (Array Name) := do
  let arg := doReassign[0]
  if arg.getKind == ``Lean.Parser.Term.letIdDecl then
    pure #[getLetIdDeclVar arg]
  else if arg.getKind == ``Lean.Parser.Term.letPatDecl then
    getLetPatDeclVars arg
  else
    throwError "unexpected kind of reassignment"

def mkDoSeq (doElems : Array Syntax) : Syntax :=
  mkNode `Lean.Parser.Term.doSeqIndent #[mkNullNode $ doElems.map fun doElem => mkNullNode #[doElem, mkNullNode]]

def mkSingletonDoSeq (doElem : Syntax) : Syntax :=
  mkDoSeq #[doElem]

/-
  If the given syntax is a `doIf`, return an equivalente `doIf` that has an `else` but no `else if`s or `if let`s.  -/
private def expandDoIf? (stx : Syntax) : MacroM (Option Syntax) := match stx with
  | `(doElem|if $p:doIfProp then $t else $e) => pure none
  | `(doElem|if%$i $cond:doIfCond then $t $[else if%$is $conds:doIfCond then $ts]* $[else $e?]?) => withRef stx do
    let mut e      := e?.getD (← `(doSeq|pure PUnit.unit))
    let mut eIsSeq := true
    for (i, cond, t) in Array.zip (is.reverse.push i) (Array.zip (conds.reverse.push cond) (ts.reverse.push t)) do
      e ← if eIsSeq then e else `(doSeq|$e:doElem)
      e ← withRef cond <| match cond with
        | `(doIfCond|let $pat := $d) => `(doElem| match%$i $d:term with | $pat:term => $t | _ => $e)
        | `(doIfCond|let $pat ← $d)  => `(doElem| match%$i ← $d    with | $pat:term => $t | _ => $e)
        | `(doIfCond|$cond:doIfProp) => `(doElem| if%$i $cond:doIfProp then $t else $e)
        | _                          => `(doElem| if%$i $(Syntax.missing) then $t else $e)
      eIsSeq := false
    return some e
  | _ => pure none

structure DoIfView where
  ref        : Syntax
  optIdent   : Syntax
  cond       : Syntax
  thenBranch : Syntax
  elseBranch : Syntax

/- This method assumes `expandDoIf?` is not applicable. -/
private def mkDoIfView (doIf : Syntax) : MacroM DoIfView := do
  pure {
    ref        := doIf,
    optIdent   := doIf[1][0],
    cond       := doIf[1][1],
    thenBranch := doIf[3],
    elseBranch := doIf[5][1]
  }

/-
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
    pure elems[0]
  else
    (elems.extract 0 (elems.size - 1)).foldrM
      (fun elem tuple => ``(MProd.mk $elem $tuple))
      (elems.back)

/- Return `some action` if `doElem` is a `doExpr <action>`-/
def isDoExpr? (doElem : Syntax) : Option Syntax :=
  if doElem.getKind == ``Lean.Parser.Term.doExpr then
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
private def destructTuple (uvars : Array Name) (x : Syntax) (body : Syntax) : MacroM Syntax := do
  if uvars.size == 0 then
    return body
  else if uvars.size == 1 then
    `(let $(← mkIdentFromRef uvars[0]):ident := $x; $body)
  else
    destruct uvars.toList x body
where
  destruct (as : List Name) (x : Syntax) (body : Syntax) : MacroM Syntax := do
    match as with
      | [a, b]  => `(let $(← mkIdentFromRef a):ident := $x.1; let $(← mkIdentFromRef b):ident := $x.2; $body)
      | a :: as => withFreshMacroScope do
        let rest ← destruct as (← `(x)) body
        `(let $(← mkIdentFromRef a):ident := $x.1; let x := $x.2; $rest)
      | _ => unreachable!

/-
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
  | Kind.regular => true
  | _            => false

structure Context where
  m     : Syntax -- Syntax to reference the monad associated with the do notation.
  uvars : Array Name
  kind  : Kind

abbrev M := ReaderT Context MacroM

def mkUVarTuple : M Syntax := do
  let ctx ← read
  let uvarIdents ← ctx.uvars.mapM mkIdentFromRef
  mkTuple uvarIdents

def returnToTerm (val : Syntax) : M Syntax := do
  let ctx ← read
  let u ← mkUVarTuple
  match ctx.kind with
  | Kind.regular         => if ctx.uvars.isEmpty then ``(Pure.pure $val) else ``(Pure.pure (MProd.mk $val $u))
  | Kind.forIn           => ``(Pure.pure (ForInStep.done $u))
  | Kind.forInWithReturn => ``(Pure.pure (ForInStep.done (MProd.mk (some $val) $u)))
  | Kind.nestedBC        => unreachable!
  | Kind.nestedPR        => ``(Pure.pure (DoResultPR.«return» $val $u))
  | Kind.nestedSBC       => ``(Pure.pure (DoResultSBC.«pureReturn» $val $u))
  | Kind.nestedPRBC      => ``(Pure.pure (DoResultPRBC.«return» $val $u))

def continueToTerm : M Syntax := do
  let ctx ← read
  let u ← mkUVarTuple
  match ctx.kind with
  | Kind.regular         => unreachable!
  | Kind.forIn           => ``(Pure.pure (ForInStep.yield $u))
  | Kind.forInWithReturn => ``(Pure.pure (ForInStep.yield (MProd.mk none $u)))
  | Kind.nestedBC        => ``(Pure.pure (DoResultBC.«continue» $u))
  | Kind.nestedPR        => unreachable!
  | Kind.nestedSBC       => ``(Pure.pure (DoResultSBC.«continue» $u))
  | Kind.nestedPRBC      => ``(Pure.pure (DoResultPRBC.«continue» $u))

def breakToTerm : M Syntax := do
  let ctx ← read
  let u ← mkUVarTuple
  match ctx.kind with
  | Kind.regular         => unreachable!
  | Kind.forIn           => ``(Pure.pure (ForInStep.done $u))
  | Kind.forInWithReturn => ``(Pure.pure (ForInStep.done (MProd.mk none $u)))
  | Kind.nestedBC        => ``(Pure.pure (DoResultBC.«break» $u))
  | Kind.nestedPR        => unreachable!
  | Kind.nestedSBC       => ``(Pure.pure (DoResultSBC.«break» $u))
  | Kind.nestedPRBC      => ``(Pure.pure (DoResultPRBC.«break» $u))

def actionTerminalToTerm (action : Syntax) : M Syntax := withRef action <| withFreshMacroScope do
  let ctx ← read
  let u ← mkUVarTuple
  match ctx.kind with
  | Kind.regular         => if ctx.uvars.isEmpty then pure action else ``(Bind.bind $action fun y => Pure.pure (MProd.mk y $u))
  | Kind.forIn           => ``(Bind.bind $action fun (_ : PUnit) => Pure.pure (ForInStep.yield $u))
  | Kind.forInWithReturn => ``(Bind.bind $action fun (_ : PUnit) => Pure.pure (ForInStep.yield (MProd.mk none $u)))
  | Kind.nestedBC        => unreachable!
  | Kind.nestedPR        => ``(Bind.bind $action fun y => (Pure.pure (DoResultPR.«pure» y $u)))
  | Kind.nestedSBC       => ``(Bind.bind $action fun y => (Pure.pure (DoResultSBC.«pureReturn» y $u)))
  | Kind.nestedPRBC      => ``(Bind.bind $action fun y => (Pure.pure (DoResultPRBC.«pure» y $u)))

def seqToTerm (action : Syntax) (k : Syntax) : M Syntax := withRef action <| withFreshMacroScope do
  if action.getKind == ``Lean.Parser.Term.doDbgTrace then
    let msg := action[1]
    `(dbg_trace $msg; $k)
  else if action.getKind == ``Lean.Parser.Term.doAssert then
    let cond := action[1]
    `(assert! $cond; $k)
  else
    let action ← withRef action ``(($action : $((←read).m) PUnit))
    ``(Bind.bind $action (fun (_ : PUnit) => $k))

def declToTerm (decl : Syntax) (k : Syntax) : M Syntax := withRef decl <| withFreshMacroScope do
  let kind := decl.getKind
  if kind == ``Lean.Parser.Term.doLet then
    let letDecl := decl[2]
    `(let $letDecl:letDecl; $k)
  else if kind == ``Lean.Parser.Term.doLetRec then
    let letRecToken := decl[0]
    let letRecDecls := decl[1]
    pure $ mkNode ``Lean.Parser.Term.letrec #[letRecToken, letRecDecls, mkNullNode, k]
  else if kind == ``Lean.Parser.Term.doLetArrow then
    let arg := decl[2]
    let ref := arg
    if arg.getKind == ``Lean.Parser.Term.doIdDecl then
      let id     := arg[0]
      let type   := expandOptType id arg[1]
      let doElem := arg[3]
      -- `doElem` must be a `doExpr action`. See `doLetArrowToCode`
      match isDoExpr? doElem with
      | some action =>
        let action ← withRef action `(($action : $((← read).m) $type))
        ``(Bind.bind $action (fun ($id:ident : $type) => $k))
      | none        => Macro.throwErrorAt decl "unexpected kind of 'do' declaration"
    else
      Macro.throwErrorAt decl "unexpected kind of 'do' declaration"
  else if kind == ``Lean.Parser.Term.doHave then
    -- The `have` term is of the form  `"have " >> haveDecl >> optSemicolon termParser`
    let args := decl.getArgs
    let args := args ++ #[mkNullNode /- optional ';' -/, k]
    pure $ mkNode `Lean.Parser.Term.«have» args
  else
    Macro.throwErrorAt decl "unexpected kind of 'do' declaration"

def reassignToTerm (reassign : Syntax) (k : Syntax) : MacroM Syntax := withRef reassign <| withFreshMacroScope do
  let kind := reassign.getKind
  if kind == ``Lean.Parser.Term.doReassign then
    -- doReassign := leading_parser (letIdDecl <|> letPatDecl)
    let arg := reassign[0]
    if arg.getKind == ``Lean.Parser.Term.letIdDecl then
      -- letIdDecl := leading_parser ident >> many (ppSpace >> bracketedBinder) >> optType >>  " := " >> termParser
      let x   := arg[0]
      let val := arg[4]
      let newVal ← `(ensureTypeOf% $x $(quote "invalid reassignment, value") $val)
      let arg := arg.setArg 4 newVal
      let letDecl := mkNode `Lean.Parser.Term.letDecl #[arg]
      `(let $letDecl:letDecl; $k)
    else
      -- TODO: ensure the types did not change
      let letDecl := mkNode `Lean.Parser.Term.letDecl #[arg]
      `(let $letDecl:letDecl; $k)
  else
    -- Note that `doReassignArrow` is expanded by `doReassignArrowToCode
    Macro.throwErrorAt reassign "unexpected kind of 'do' reassignment"

def mkIte (optIdent : Syntax) (cond : Syntax) (thenBranch : Syntax) (elseBranch : Syntax) : MacroM Syntax := do
  if optIdent.isNone then
    ``(ite $cond $thenBranch $elseBranch)
  else
    let h := optIdent[0]
    ``(dite $cond (fun $h => $thenBranch) (fun $h => $elseBranch))

def mkJoinPoint (j : Name) (ps : Array (Name × Bool)) (body : Syntax) (k : Syntax) : M Syntax := withRef body <| withFreshMacroScope do
  let pTypes ← ps.mapM fun ⟨id, useTypeOf⟩ => do if useTypeOf then `(typeOf% $(← mkIdentFromRef id)) else `(_)
  let ps     ← ps.mapM fun ⟨id, useTypeOf⟩ => mkIdentFromRef id
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

partial def toTerm : Code → M Syntax
  | Code.«return» ref val   => withRef ref <| returnToTerm val
  | Code.«continue» ref     => withRef ref continueToTerm
  | Code.«break» ref        => withRef ref breakToTerm
  | Code.action e           => actionTerminalToTerm e
  | Code.joinpoint j ps b k => do mkJoinPoint j ps (← toTerm b) (← toTerm k)
  | Code.jmp ref j args     => pure $ mkJmp ref j args
  | Code.decl _ stx k       => do declToTerm stx (← toTerm k)
  | Code.reassign _ stx k   => do reassignToTerm stx (← toTerm k)
  | Code.seq stx k          => do seqToTerm stx (← toTerm k)
  | Code.ite ref _ o c t e  => withRef ref <| do mkIte o c (← toTerm t) (← toTerm e)
  | Code.«match» ref genParam discrs optType alts => do
    let mut termAlts := #[]
    for alt in alts do
      let rhs ← toTerm alt.rhs
      let termAlt := mkNode `Lean.Parser.Term.matchAlt #[mkAtomFrom alt.ref "|", alt.patterns, mkAtomFrom alt.ref "=>", rhs]
      termAlts := termAlts.push termAlt
    let termMatchAlts := mkNode `Lean.Parser.Term.matchAlts #[mkNullNode termAlts]
    pure $ mkNode `Lean.Parser.Term.«match» #[mkAtomFrom ref "match", genParam, discrs, optType, mkAtomFrom ref "with", termMatchAlts]

def run (code : Code) (m : Syntax) (uvars : Array Name := #[]) (kind := Kind.regular) : MacroM Syntax := do
  let term ← toTerm code { m := m, kind := kind, uvars := uvars }
  pure term

/- Given
   - `a` is true if the code block has a `Code.action _` exit point
   - `r` is true if the code block has a `Code.return _ _` exit point
   - `bc` is true if the code block has a `Code.break _` or `Code.continue _` exit point

   generate Kind. See comment at the beginning of the `ToTerm` namespace. -/
def mkNestedKind (a r bc : Bool) : Kind :=
  match a, r, bc with
  | true,  false, false => Kind.regular
  | false, true,  false => Kind.regular
  | false, false, true  => Kind.nestedBC
  | true,  true,  false => Kind.nestedPR
  | true,  false, true  => Kind.nestedSBC
  | false, true,  true  => Kind.nestedSBC
  | true,  true,  true  => Kind.nestedPRBC
  | false, false, false => unreachable!

def mkNestedTerm (code : Code) (m : Syntax) (uvars : Array Name) (a r bc : Bool) : MacroM Syntax := do
  ToTerm.run code m uvars (mkNestedKind a r bc)

/- Given a term `term` produced by `ToTerm.run`, pattern match on its result.
   See comment at the beginning of the `ToTerm` namespace.

   - `a` is true if the code block has a `Code.action _` exit point
   - `r` is true if the code block has a `Code.return _ _` exit point
   - `bc` is true if the code block has a `Code.break _` or `Code.continue _` exit point

   The result is a sequence of `doElem` -/
def matchNestedTermResult (term : Syntax) (uvars : Array Name) (a r bc : Bool) : MacroM (List Syntax) := do
  let toDoElems (auxDo : Syntax) : List Syntax := getDoSeqElems (getDoSeq auxDo)
  let u ← mkTuple (← uvars.mapM mkIdentFromRef)
  match a, r, bc with
  | true, false, false =>
    if uvars.isEmpty then
      toDoElems (← `(do $term:term))
    else
      toDoElems (← `(do let r ← $term:term; $u:term := r.2; pure r.1))
  | false, true, false =>
    if uvars.isEmpty then
      toDoElems (← `(do let r ← $term:term; return r))
    else
      toDoElems (← `(do let r ← $term:term; $u:term := r.2; return r.1))
  | false, false, true => toDoElems <$>
    `(do let r ← $term:term;
         match r with
         | DoResultBC.«break» u => $u:term := u; break
         | DoResultBC.«continue» u => $u:term := u; continue)
  | true, true, false => toDoElems <$>
    `(do let r ← $term:term;
         match r with
         | DoResultPR.«pure» a u => $u:term := u; pure a
         | DoResultPR.«return» b u => $u:term := u; return b)
  | true, false, true => toDoElems <$>
    `(do let r ← $term:term;
         match r with
         | DoResultSBC.«pureReturn» a u => $u:term := u; pure a
         | DoResultSBC.«break» u => $u:term := u; break
         | DoResultSBC.«continue» u => $u:term := u; continue)
  | false, true, true => toDoElems <$>
    `(do let r ← $term:term;
         match r with
         | DoResultSBC.«pureReturn» a u => $u:term := u; return a
         | DoResultSBC.«break» u => $u:term := u; break
         | DoResultSBC.«continue» u => $u:term := u; continue)
  | true, true, true => toDoElems <$>
    `(do let r ← $term:term;
         match r with
         | DoResultPRBC.«pure» a u => $u:term := u; pure a
         | DoResultPRBC.«return» a u => $u:term := u; return a
         | DoResultPRBC.«break» u => $u:term := u; break
         | DoResultPRBC.«continue» u => $u:term := u; continue)
  | false, false, false => unreachable!

end ToTerm

def isMutableLet (doElem : Syntax) : Bool :=
  let kind := doElem.getKind
  (kind == `Lean.Parser.Term.doLetArrow || kind == `Lean.Parser.Term.doLet)
  &&
  !doElem[1].isNone

namespace ToCodeBlock

structure Context where
  ref         : Syntax
  m           : Syntax -- Syntax representing the monad associated with the do notation.
  mutableVars : NameSet := {}
  insideFor   : Bool := false

abbrev M := ReaderT Context TermElabM

def withNewMutableVars {α} (newVars : Array Name) (mutable : Bool) (x : M α) : M α :=
  withReader (fun ctx => if mutable then { ctx with mutableVars := insertVars ctx.mutableVars newVars } else ctx) x

def checkReassignable (xs : Array Name) : M Unit := do
  let throwInvalidReassignment (x : Name) : M Unit :=
    throwError "'{x.simpMacroScopes}' cannot be reassigned"
  let ctx ← read
  for x in xs do
    unless ctx.mutableVars.contains x do
      throwInvalidReassignment x

def checkNotShadowingMutable (xs : Array Name) : M Unit := do
  let throwInvalidShadowing (x : Name) : M Unit :=
    throwError "mutable variable '{x.simpMacroScopes}' cannot be shadowed"
  let ctx ← read
  for x in xs do
    if ctx.mutableVars.contains x then
      throwInvalidShadowing x

def withFor {α} (x : M α) : M α :=
  withReader (fun ctx => { ctx with insideFor := true }) x

structure ToForInTermResult where
  uvars      : Array Name
  term       : Syntax

def mkForInBody  (x : Syntax) (forInBody : CodeBlock) : M ToForInTermResult := do
  let ctx ← read
  let uvars := forInBody.uvars
  let uvars := nameSetToArray uvars
  let term ← liftMacroM $ ToTerm.run forInBody.code ctx.m uvars (if hasReturn forInBody.code then ToTerm.Kind.forInWithReturn else ToTerm.Kind.forIn)
  pure ⟨uvars, term⟩

def ensureInsideFor : M Unit :=
  unless (← read).insideFor do
    throwError "invalid 'do' element, it must be inside 'for'"

def ensureEOS (doElems : List Syntax) : M Unit :=
  unless doElems.isEmpty do
    throwError "must be last element in a 'do' sequence"

private partial def expandLiftMethodAux (inQuot : Bool) (inBinder : Bool) : Syntax → StateT (List Syntax) M Syntax
  | stx@(Syntax.node k args) =>
    if liftMethodDelimiter k then
      return stx
    else if k == ``Lean.Parser.Term.liftMethod && !inQuot then withFreshMacroScope do
      if inBinder then
        throwErrorAt stx "cannot lift `(<- ...)` over a binder, this error usually happens when you are trying to lift a method nested in a `fun`, `let`, or `match`-alternative, and it can often be fixed by adding a missing `do`"
      let term := args[1]
      let term ← expandLiftMethodAux inQuot inBinder term
      let auxDoElem ← `(doElem| let a ← $term:term)
      modify fun s => s ++ [auxDoElem]
      `(a)
    else do
      let inAntiquot := stx.isAntiquot && !stx.isEscapedAntiquot
      let inBinder   := inBinder || (!inQuot && liftMethodForbiddenBinder stx)
      let args ← args.mapM (expandLiftMethodAux (inQuot && !inAntiquot || stx.isQuot) inBinder)
      return Syntax.node k args
  | stx => pure stx

def expandLiftMethod (doElem : Syntax) : M (List Syntax × Syntax) := do
  if !hasLiftMethod doElem then
    pure ([], doElem)
  else
    let (doElem, doElemsNew) ← (expandLiftMethodAux false false doElem).run []
    pure (doElemsNew, doElem)

def checkLetArrowRHS (doElem : Syntax) : M Unit := do
  let kind := doElem.getKind
  if kind == ``Lean.Parser.Term.doLetArrow ||
     kind == ``Lean.Parser.Term.doLet ||
     kind == ``Lean.Parser.Term.doLetRec ||
     kind == ``Lean.Parser.Term.doHave ||
     kind == ``Lean.Parser.Term.doReassign ||
     kind == ``Lean.Parser.Term.doReassignArrow then
    throwErrorAt doElem "invalid kind of value '{kind}' in an assignment"

/- Generate `CodeBlock` for `doReturn` which is of the form
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

def getTryCatchUpdatedVars (tryCode : CodeBlock) (catches : Array Catch) (finallyCode? : Option CodeBlock) : NameSet :=
  let ws := tryCode.uvars
  let ws := catches.foldl (fun ws alt => union alt.codeBlock.uvars ws) ws
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
  /- "Concatenate" `c` with `doSeqToCode doElems` -/
  partial def concatWith (c : CodeBlock) (doElems : List Syntax) : M CodeBlock :=
    match doElems with
    | [] => pure c
    | nextDoElem :: _  => do
      let k ← doSeqToCode doElems
      let ref := nextDoElem
      concat c ref none k

  /- Generate `CodeBlock` for `doLetArrow; doElems`
     `doLetArrow` is of the form
     ```
     "let " >> optional "mut " >> (doIdDecl <|> doPatDecl)
     ```
     where
     ```
     def doIdDecl   := leading_parser ident >> optType >> leftArrow >> doElemParser
     def doPatDecl  := leading_parser termParser >> leftArrow >> doElemParser >> optional (" | " >> doElemParser)
     ```
  -/
  partial def doLetArrowToCode (doLetArrow : Syntax) (doElems : List Syntax) : M CodeBlock := do
    let ref     := doLetArrow
    let decl    := doLetArrow[2]
    if decl.getKind == ``Lean.Parser.Term.doIdDecl then
      let y := decl[0].getId
      checkNotShadowingMutable #[y]
      let doElem := decl[3]
      let k ← withNewMutableVars #[y] (isMutableLet doLetArrow) (doSeqToCode doElems)
      match isDoExpr? doElem with
      | some action => pure $ mkVarDeclCore #[y] doLetArrow k
      | none =>
        checkLetArrowRHS doElem
        let c ← doSeqToCode [doElem]
        match doElems with
        | []       => pure c
        | kRef::_  => concat c kRef y k
    else if decl.getKind == ``Lean.Parser.Term.doPatDecl then
      let pattern := decl[0]
      let doElem  := decl[2]
      let optElse := decl[3]
      if optElse.isNone then withFreshMacroScope do
        let auxDo ←
          if isMutableLet doLetArrow then
            `(do let discr ← $doElem; let mut $pattern:term := discr)
          else
            `(do let discr ← $doElem; let $pattern:term := discr)
        doSeqToCode <| getDoSeqElems (getDoSeq auxDo) ++ doElems
      else
        if isMutableLet doLetArrow then
          throwError "'mut' is currently not supported in let-decls with 'else' case"
        let contSeq := mkDoSeq doElems.toArray
        let elseSeq := mkSingletonDoSeq optElse[1]
        let auxDo ← `(do let discr ← $doElem; match discr with | $pattern:term => $contSeq | _ => $elseSeq)
        doSeqToCode <| getDoSeqElems (getDoSeq auxDo)
    else
      throwError "unexpected kind of 'do' declaration"


  /- Generate `CodeBlock` for `doReassignArrow; doElems`
     `doReassignArrow` is of the form
     ```
     (doIdDecl <|> doPatDecl)
     ```
  -/
  partial def doReassignArrowToCode (doReassignArrow : Syntax) (doElems : List Syntax) : M CodeBlock := do
    let ref  := doReassignArrow
    let decl := doReassignArrow[0]
    if decl.getKind == ``Lean.Parser.Term.doIdDecl then
      let doElem := decl[3]
      let y      := decl[0]
      let auxDo ← `(do let r ← $doElem; $y:ident := r)
      doSeqToCode <| getDoSeqElems (getDoSeq auxDo) ++ doElems
    else if decl.getKind == ``Lean.Parser.Term.doPatDecl then
      let pattern := decl[0]
      let doElem  := decl[2]
      let optElse := decl[3]
      if optElse.isNone then withFreshMacroScope do
        let auxDo ← `(do let discr ← $doElem; $pattern:term := discr)
        doSeqToCode <| getDoSeqElems (getDoSeq auxDo) ++ doElems
      else
        throwError "reassignment with `|` (i.e., \"else clause\") is not currently supported"
    else
      throwError "unexpected kind of 'do' reassignment"

  /- Generate `CodeBlock` for `doIf; doElems`
     `doIf` is of the form
     ```
     "if " >> optIdent >> termParser >> " then " >> doSeq
      >> many (group (try (group (" else " >> " if ")) >> optIdent >> termParser >> " then " >> doSeq))
      >> optional (" else " >> doSeq)
     ```  -/
  partial def doIfToCode (doIf : Syntax) (doElems : List Syntax) : M CodeBlock := do
    let view ← liftMacroM $ mkDoIfView doIf
    let thenBranch ← doSeqToCode (getDoSeqElems view.thenBranch)
    let elseBranch ← doSeqToCode (getDoSeqElems view.elseBranch)
    let ite ← mkIte view.ref view.optIdent view.cond thenBranch elseBranch
    concatWith ite doElems

  /- Generate `CodeBlock` for `doUnless; doElems`
     `doUnless` is of the form
     ```
     "unless " >> termParser >> "do " >> doSeq
     ```  -/
  partial def doUnlessToCode (doUnless : Syntax) (doElems : List Syntax) : M CodeBlock := withRef doUnless do
    let ref   := doUnless
    let cond  := doUnless[1]
    let doSeq := doUnless[3]
    let body ← doSeqToCode (getDoSeqElems doSeq)
    let unlessCode ← liftMacroM <| mkUnless cond body
    concatWith unlessCode doElems

  /- Generate `CodeBlock` for `doFor; doElems`
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
      let doForDecl := doForDecls[1]
      let y  := doForDecl[0]
      let ys := doForDecl[2]
      let doForDecls := doForDecls.eraseIdx 1
      let body := doFor[3]
      withFreshMacroScope do
        let toStreamFn ← withRef ys ``(toStream)
        let auxDo ←
          `(do let mut s := $toStreamFn:ident $ys
               for $doForDecls:doForDecl,* do
                 match Stream.next? s with
                 | none => break
                 | some ($y, s') =>
                   s := s'
                   do $body)
        doSeqToCode (getDoSeqElems (getDoSeq auxDo) ++ doElems)
    else withRef doFor do
      let x         := doForDecls[0][0]
      withRef x <| checkNotShadowingMutable (← getPatternVarsEx x)
      let xs        := doForDecls[0][2]
      let forElems  := getDoSeqElems doFor[3]
      let forInBodyCodeBlock ← withFor (doSeqToCode forElems)
      let ⟨uvars, forInBody⟩ ← mkForInBody x forInBodyCodeBlock
      let uvarsTuple ← liftMacroM do mkTuple (← uvars.mapM mkIdentFromRef)
      if hasReturn forInBodyCodeBlock.code then
        let forInBody ← liftMacroM <| destructTuple uvars (← `(r)) forInBody
        let forInTerm ← `(forIn% $(xs) (MProd.mk none $uvarsTuple) fun $x r => let r := r.2; $forInBody)
        let auxDo ← `(do let r ← $forInTerm:term;
                         $uvarsTuple:term := r.2;
                         match r.1 with
                         | none => Pure.pure (ensureExpectedType% "type mismatch, 'for'" PUnit.unit)
                         | some a => return ensureExpectedType% "type mismatch, 'for'" a)
        doSeqToCode (getDoSeqElems (getDoSeq auxDo) ++ doElems)
      else
        let forInBody ← liftMacroM <| destructTuple uvars (← `(r)) forInBody
        let forInTerm ← `(forIn% $(xs) $uvarsTuple fun $x r => $forInBody)
        if doElems.isEmpty then
          let auxDo ← `(do let r ← $forInTerm:term;
                           $uvarsTuple:term := r;
                           Pure.pure (ensureExpectedType% "type mismatch, 'for'" PUnit.unit))
          doSeqToCode <| getDoSeqElems (getDoSeq auxDo)
        else
          let auxDo ← `(do let r ← $forInTerm:term; $uvarsTuple:term := r)
          doSeqToCode <| getDoSeqElems (getDoSeq auxDo) ++ doElems

  /-- Generate `CodeBlock` for `doMatch; doElems` -/
  partial def doMatchToCode (doMatch : Syntax) (doElems: List Syntax) : M CodeBlock := do
    let ref       := doMatch
    let genParam  := doMatch[1]
    let discrs    := doMatch[2]
    let optType   := doMatch[3]
    let matchAlts := doMatch[5][0].getArgs -- Array of `doMatchAlt`
    let alts ←  matchAlts.mapM fun matchAlt => do
      let patterns := matchAlt[1]
      let vars ← getPatternsVarsEx patterns.getSepArgs
      withRef patterns <| checkNotShadowingMutable vars
      let rhs  := matchAlt[3]
      let rhs ← doSeqToCode (getDoSeqElems rhs)
      pure { ref := matchAlt, vars := vars, patterns := patterns, rhs := rhs : Alt CodeBlock }
    let matchCode ← mkMatch ref genParam discrs optType alts
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
    let ref := doTry
    let tryCode ← doSeqToCode (getDoSeqElems doTry[1])
    let optFinally := doTry[3]
    let catches ← doTry[2].getArgs.mapM fun catchStx => do
      if catchStx.getKind == ``Lean.Parser.Term.doCatch then
        let x       := catchStx[1]
        if x.isIdent then
          withRef x <| checkNotShadowingMutable #[x.getId]
        let optType := catchStx[2]
        let c ← doSeqToCode (getDoSeqElems catchStx[4])
        pure { x := x, optType := optType, codeBlock := c : Catch }
      else if catchStx.getKind == ``Lean.Parser.Term.doCatchMatch then
        let matchAlts := catchStx[1]
        let x ← `(ex)
        let auxDo ← `(do match ex with $matchAlts)
        let c ← doSeqToCode (getDoSeqElems (getDoSeq auxDo))
        pure { x := x, codeBlock := c, optType := mkNullNode : Catch }
      else
        throwError "unexpected kind of 'catch'"
    let finallyCode? ← if optFinally.isNone then pure none else some <$> doSeqToCode (getDoSeqElems optFinally[0][1])
    if catches.isEmpty && finallyCode?.isNone then
      throwError "invalid 'try', it must have a 'catch' or 'finally'"
    let ctx ← read
    let ws    := getTryCatchUpdatedVars tryCode catches finallyCode?
    let uvars := nameSetToArray ws
    let a     := tryCatchPred tryCode catches finallyCode? hasTerminalAction
    let r     := tryCatchPred tryCode catches finallyCode? hasReturn
    let bc    := tryCatchPred tryCode catches finallyCode? hasBreakContinue
    let toTerm (codeBlock : CodeBlock) : M Syntax := do
      let codeBlock ← liftM $ extendUpdatedVars codeBlock ws
      liftMacroM $ ToTerm.mkNestedTerm codeBlock.code ctx.m uvars a r bc
    let term ← toTerm tryCode
    let term ← catches.foldlM
      (fun term «catch» => do
        let catchTerm ← toTerm «catch».codeBlock
        if catch.optType.isNone then
          ``(MonadExcept.tryCatch $term (fun $(«catch».x):ident => $catchTerm))
        else
          let type := «catch».optType[1]
          ``(tryCatchThe $type $term (fun $(«catch».x):ident => $catchTerm)))
      term
    let term ← match finallyCode? with
      | none             => pure term
      | some finallyCode => withRef optFinally do
        unless finallyCode.uvars.isEmpty do
          throwError "'finally' currently does not support reassignments"
        if hasBreakContinueReturn finallyCode.code then
          throwError "'finally' currently does 'return', 'break', nor 'continue'"
        let finallyTerm ← liftMacroM <| ToTerm.run finallyCode.code ctx.m {} ToTerm.Kind.regular
        ``(tryFinally $term $finallyTerm)
    let doElemsNew ← liftMacroM <| ToTerm.matchNestedTermResult term uvars a r bc
    doSeqToCode (doElemsNew ++ doElems)

  partial def doSeqToCode : List Syntax → M CodeBlock
    | [] => do liftMacroM mkPureUnitAction
    | doElem::doElems => withIncRecDepth <| withRef doElem do
      checkMaxHeartbeats "'do'-expander"
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
          let concatWithRest (c : CodeBlock) : M CodeBlock := concatWith c doElems
          let k := doElem.getKind
          if k == ``Lean.Parser.Term.doLet then
            let vars ← getDoLetVars doElem
            checkNotShadowingMutable vars
            mkVarDeclCore vars doElem <$> withNewMutableVars vars (isMutableLet doElem) (doSeqToCode doElems)
          else if k == ``Lean.Parser.Term.doHave then
            let var := getDoHaveVar doElem
            checkNotShadowingMutable #[var]
            mkVarDeclCore #[var] doElem <$> (doSeqToCode doElems)
          else if k == ``Lean.Parser.Term.doLetRec then
            let vars ← getDoLetRecVars doElem
            checkNotShadowingMutable vars
            mkVarDeclCore vars doElem <$> (doSeqToCode doElems)
          else if k == ``Lean.Parser.Term.doReassign then
            let vars ← getDoReassignVars doElem
            checkReassignable vars
            let k ← doSeqToCode doElems
            mkReassignCore vars doElem k
          else if k == ``Lean.Parser.Term.doLetArrow then
            doLetArrowToCode doElem doElems
          else if k == ``Lean.Parser.Term.doReassignArrow then
            doReassignArrowToCode doElem doElems
          else if k == ``Lean.Parser.Term.doIf then
            doIfToCode doElem doElems
          else if k == ``Lean.Parser.Term.doUnless then
            doUnlessToCode doElem doElems
          else if k == ``Lean.Parser.Term.doFor then withFreshMacroScope do
            doForToCode doElem doElems
          else if k == ``Lean.Parser.Term.doMatch then
            doMatchToCode doElem doElems
          else if k == ``Lean.Parser.Term.doTry then
            doTryToCode doElem doElems
          else if k == ``Lean.Parser.Term.doBreak then
            ensureInsideFor
            ensureEOS doElems
            return mkBreak ref
          else if k == ``Lean.Parser.Term.doContinue then
            ensureInsideFor
            ensureEOS doElems
            return mkContinue ref
          else if k == ``Lean.Parser.Term.doReturn then
            doReturnToCode doElem doElems
          else if k == ``Lean.Parser.Term.doDbgTrace then
            return mkSeq doElem (← doSeqToCode doElems)
          else if k == ``Lean.Parser.Term.doAssert then
            return mkSeq doElem (← doSeqToCode doElems)
          else if k == ``Lean.Parser.Term.doNested then
            let nestedDoSeq := doElem[1]
            doSeqToCode (getDoSeqElems nestedDoSeq ++ doElems)
          else if k == ``Lean.Parser.Term.doExpr then
            let term := doElem[0]
            if doElems.isEmpty then
              return mkTerminalAction term
            else
              return mkSeq term (← doSeqToCode doElems)
          else
            throwError "unexpected do-element of kind {doElem.getKind}:\n{doElem}"
end

def run (doStx : Syntax) (m : Syntax) : TermElabM CodeBlock :=
  (doSeqToCode <| getDoSeqElems <| getDoSeq doStx).run { ref := doStx, m }

end ToCodeBlock

/- Create a synthetic metavariable `?m` and assign `m` to it.
   We use `?m` to refer to `m` when expanding the `do` notation. -/
private def mkMonadAlias (m : Expr) : TermElabM Syntax := do
  let result ← `(?m)
  let mType ← inferType m
  let mvar ← elabTerm result mType
  assignExprMVar mvar.mvarId! m
  pure result

private partial def ensureArrowNotUsed (stx : Syntax) : MacroM Unit := do
  /- We expand macros here because we stop the search at nested `do`s
     So, we also want to stop the search at macros that expand `do ...`.
     Hopefully this is not a performance bottleneck in practice. -/
  let stx ← expandMacros stx
  stx.getArgs.forM go
where
  go (stx : Syntax) : MacroM Unit :=
    match stx with
    | Syntax.node k args => do
      if k == ``Parser.Term.liftMethod || k == ``Parser.Term.doLetArrow || k == ``Parser.Term.doReassignArrow || k == ``Parser.Term.doIfLetBind then
        Macro.throwErrorAt stx "`←` and `<-` are not allowed in pure `do` blocks, i.e., blocks where Lean implicitly used the `Id` monad"
      unless k == ``Parser.Term.do do
        args.forM go
    | _ => pure ()

@[builtinTermElab «do»] def elabDo : TermElab := fun stx expectedType? => do
  tryPostponeIfNoneOrMVar expectedType?
  let bindInfo ← extractBind expectedType?
  if bindInfo.isPure then
    liftMacroM <| ensureArrowNotUsed stx
  let m ← mkMonadAlias bindInfo.m
  let codeBlock ← ToCodeBlock.run stx m
  let stxNew ← liftMacroM $ ToTerm.run codeBlock.code m
  trace[Elab.do] stxNew
  withMacroExpansion stx stxNew $ elabTermEnsuringType stxNew bindInfo.expectedType

end Do

builtin_initialize registerTraceClass `Elab.do

private def toDoElem (newKind : SyntaxNodeKind) : Macro := fun stx => do
  let stx := stx.setKind newKind
  withRef stx `(do $stx:doElem)

@[builtinMacro Lean.Parser.Term.termFor]
def expandTermFor : Macro := toDoElem ``Lean.Parser.Term.doFor

@[builtinMacro Lean.Parser.Term.termTry]
def expandTermTry : Macro := toDoElem ``Lean.Parser.Term.doTry

@[builtinMacro Lean.Parser.Term.termUnless]
def expandTermUnless : Macro := toDoElem ``Lean.Parser.Term.doUnless

@[builtinMacro Lean.Parser.Term.termReturn]
def expandTermReturn : Macro := toDoElem ``Lean.Parser.Term.doReturn

end Lean.Elab.Term
