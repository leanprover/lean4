/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Term
import Lean.Elab.Binders
import Lean.Elab.Quotation
import Lean.Elab.Match

namespace Lean
namespace Elab
namespace Term
open Meta

private def getDoSeqElems (doSeq : Syntax) : List Syntax :=
if doSeq.getKind == `Lean.Parser.Term.doSeqBracketed then
  (doSeq.getArg 1).getArgs.toList.map fun arg => arg.getArg 0
else if doSeq.getKind == `Lean.Parser.Term.doSeqIndent then
  (doSeq.getArg 0).getArgs.toList.map fun arg => arg.getArg 0
else
  []

private def getDoSeq (doStx : Syntax) : Syntax :=
doStx.getArg 1

@[builtinTermElab liftMethod] def elabLiftMethod : TermElab :=
fun stx _ =>
  throwErrorAt stx "invalid use of `(<- ...)`, must be nested inside a 'do' expression"

private partial def hasLiftMethod : Syntax → Bool
| Syntax.node k args =>
  if k == `Lean.Parser.Term.do then false
  else if k == `Lean.Parser.Term.doSeqIndent then false
  else if k == `Lean.Parser.Term.doSeqBracketed then false
  else if k == `Lean.Parser.Term.quot then false
  else if k == `Lean.Parser.Term.liftMethod then true
  else args.any hasLiftMethod
| _ => false

structure ExtractMonadResult :=
(m           : Expr)
(α           : Expr)
(hasBindInst : Expr)

private def mkIdBindFor (type : Expr) : TermElabM ExtractMonadResult := do
u ← getDecLevel type;
let id        := Lean.mkConst `Id [u];
let idBindVal := Lean.mkConst `Id.hasBind [u];
pure { m := id, hasBindInst := idBindVal, α := type }

private def extractBind (expectedType? : Option Expr) : TermElabM ExtractMonadResult := do
match expectedType? with
| none => throwError "invalid do notation, expected type is not available"
| some expectedType => do
  type ← withReducible $ whnf expectedType;
  when type.getAppFn.isMVar $ throwError "invalid do notation, expected type is not available";
  match type with
  | Expr.app m α _ =>
    catch
      (do
        bindInstType ← mkAppM `HasBind #[m];
        bindInstVal  ← synthesizeInst bindInstType;
        pure { m := m, hasBindInst := bindInstVal, α := α })
      (fun ex => mkIdBindFor type)
  | _ => mkIdBindFor type

namespace Do

/- A `doMatch` alternative. `vars` is the array of variables declared by `patterns`. -/
structure Alt (σ : Type) :=
(ref : Syntax) (vars : Array Name) (patterns : Syntax) (rhs : σ)

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
    We also store the do-elements `dbgTrace!` and `assert!` as actions in a `seq`.

  A code block `C` is well-formed if
  - For every `jmp ref j as` in `C`, there is a `joinpoint j ps b k` and `jmp ref j as` is in `k`, and
    `ps.size == as.size` -/
inductive Code
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
| «match»      (ref : Syntax) (discrs : Syntax) (optType : Syntax) (alts : Array (Alt Code))
| jmp          (ref : Syntax) (jpName : Name) (args : Array Syntax)

instance Code.inhabited : Inhabited Code :=
⟨Code.«break» (arbitrary _)⟩

instance Alt.inhabited : Inhabited (Alt Code) :=
⟨{ ref := arbitrary _, vars := #[], patterns := arbitrary _, rhs := arbitrary _ }⟩

/- A code block, and the collection of variables updated by it. -/
structure CodeBlock :=
(code  : Code)
(uvars : NameSet := {}) -- set of variables updated by `code`

private def varsToMessageData (vars : Array Name) : MessageData :=
MessageData.joinSep (vars.toList.map fun n => MessageData.ofName (n.simpMacroScopes)) " "

partial def toMessageDataAux (updateVars : MessageData) : Code → MessageData
| Code.decl xs _ k            => "let " ++ varsToMessageData xs ++ " := ... " ++ Format.line ++ toMessageDataAux k
| Code.reassign xs _ k        => varsToMessageData xs ++ " := ... " ++ Format.line ++ toMessageDataAux k
| Code.joinpoint n ps body k  =>
  "let " ++ n.simpMacroScopes ++ " " ++ varsToMessageData (ps.map Prod.fst) ++ " := " ++ indentD (toMessageDataAux body)
  ++ Format.line ++ toMessageDataAux k
| Code.seq e k              => e ++ Format.line ++ toMessageDataAux k
| Code.action e             => e
| Code.ite _ _ _ c t e      => "if " ++ c ++ " then " ++ indentD (toMessageDataAux t) ++ Format.line ++ "else " ++ indentD (toMessageDataAux e)
| Code.jmp _ j xs           => "jmp " ++ j.simpMacroScopes ++ " " ++ toString xs.toList
| Code.«break» _            => "break " ++ updateVars
| Code.«continue» _         => "continue " ++ updateVars
| Code.«return» _ v         => "return " ++ v ++ " " ++ updateVars
| Code.«match» _ ds t alts  =>
  "match " ++ ds ++ " with " ++
    alts.foldl
      (fun (acc : MessageData) (alt : Alt Code) =>
        acc ++ Format.line ++ "| " ++ alt.patterns ++ " => " ++ toMessageDataAux alt.rhs)
      Format.nil

private def nameSetToArray (s : NameSet) : Array Name :=
s.fold (fun (xs : Array Name) x => xs.push x) #[]

def CodeBlock.toMessageData (c : CodeBlock) : MessageData :=
let us := (nameSetToArray c.uvars).toList.map MessageData.ofName;
toMessageDataAux (MessageData.ofList us) c.code

/- Return true if the give code contains an exit point that satisfies `p` -/
@[specialize] partial def hasExitPointPred (p : Code → Bool) : Code → Bool
| Code.decl _ _ k         => hasExitPointPred k
| Code.reassign _ _ k     => hasExitPointPred k
| Code.joinpoint _ _ b k  => hasExitPointPred b || hasExitPointPred k
| Code.seq _ k            => hasExitPointPred k
| Code.ite _ _ _ _ t e    => hasExitPointPred t || hasExitPointPred e
| Code.«match» _ _ _ alts => alts.any fun alt => hasExitPointPred alt.rhs
| Code.jmp _ _ _          => false
| c                       => p c

def hasExitPoint (c : Code) : Bool :=
hasExitPointPred (fun c => true) c

def isReturn : Code → Bool
| Code.«return» _ _ => true
| _ => false

def hasReturn (c : Code) : Bool :=
hasExitPointPred isReturn c

def isTerminalAction : Code → Bool
| Code.«action» _ => true
| _ => false

def hasTerminalAction (c : Code) : Bool :=
hasExitPointPred isTerminalAction c

def hasBreakContinueReturn (c : Code) : Bool :=
hasExitPointPred (fun c => !isTerminalAction c) c

def mkAuxDeclFor {m} [Monad m] [MonadQuotation m] (e : Syntax) (mkCont : Syntax → m Code) : m Code := withFreshMacroScope do
y ← `(y);
let yName := y.getId;
auxDo ← `(do let y ← $e:term);
let doElem := (getDoSeqElems (getDoSeq auxDo)).head!;
-- Add elaboration hint for producing sane error message
y ← `(ensureExpectedType! "type mismatch, result value" $y);
k ← mkCont y;
pure $ Code.decl #[yName] doElem k

partial def convertTerminalActionIntoJmpAux (jp : Name) (xs : Array Name) : Code → MacroM Code
| Code.decl xs stx k         => Code.decl xs stx <$> convertTerminalActionIntoJmpAux k
| Code.reassign xs stx k     => Code.reassign xs stx <$> convertTerminalActionIntoJmpAux k
| Code.joinpoint n ps b k    => Code.joinpoint n ps <$> convertTerminalActionIntoJmpAux b <*> convertTerminalActionIntoJmpAux k
| Code.seq e k               => Code.seq e <$> convertTerminalActionIntoJmpAux k
| Code.ite ref x? h c t e    => Code.ite ref x? h c <$> convertTerminalActionIntoJmpAux t <*> convertTerminalActionIntoJmpAux e
| Code.«match» ref ds t alts => Code.«match» ref ds t <$> alts.mapM fun alt => do rhs ← convertTerminalActionIntoJmpAux alt.rhs; pure { alt with rhs := rhs }
| Code.action e              => mkAuxDeclFor e fun y =>
  let ref := e;
  -- We jump to `jp` with xs **and** y
  let jmpArgs := xs.map $ mkIdentFrom ref;
  let jmpArgs := jmpArgs.push y;
  pure $ Code.jmp ref jp jmpArgs
| c                          => pure c

/- Convert `action _ e` instructions in `c` into `let y ← e; jmp _ jp (xs y)`. -/
def convertTerminalActionIntoJmp (c : Code) (jp : Name) (xs : Array Name) : MacroM Code :=
convertTerminalActionIntoJmpAux jp xs c

structure JPDecl :=
(name : Name) (params : Array (Name × Bool)) (body : Code)

def attachJP (jpDecl : JPDecl) (k : Code) : Code :=
Code.joinpoint jpDecl.name jpDecl.params jpDecl.body k

def attachJPs (jpDecls : Array JPDecl) (k : Code) : Code :=
jpDecls.foldr attachJP k

def mkFreshJP (ps : Array (Name × Bool)) (body : Code) : TermElabM JPDecl := do
ps ←
  if ps.isEmpty then do
    y ← mkFreshUserName `y;
    pure #[(y, false)]
  else
    pure ps;
name ← mkFreshUserName `jp;
pure { name := name, params := ps, body := body }

def mkFreshJP' (xs : Array Name) (body : Code) : TermElabM JPDecl :=
mkFreshJP (xs.map fun x => (x, true)) body

def addFreshJP (ps : Array (Name × Bool)) (body : Code) : StateRefT (Array JPDecl) TermElabM Name := do
jp ← liftM $ mkFreshJP ps body;
modify fun (jps : Array JPDecl) => jps.push jp;
pure jp.name

def insertVars (rs : NameSet) (xs : Array Name) : NameSet :=
xs.foldl (fun (rs : NameSet) x => rs.insert x) rs

def eraseVars (rs : NameSet) (xs : Array Name) : NameSet :=
xs.foldl (fun (rs : NameSet) x => rs.erase x) rs

def eraseOptVar (rs : NameSet) (x? : Option Name) : NameSet :=
match x? with
| none   => rs
| some x => rs.insert x

/- Create a new jointpoint for `c`, and jump to it with the variables `rs` -/
@[inline] def mkSimpleJmp (ref : Syntax) (rs : NameSet) (c : Code) : StateRefT (Array JPDecl) TermElabM Code := do
let xs := nameSetToArray rs;
jp ← addFreshJP (xs.map fun x => (x, true)) c;
if xs.isEmpty then do
  unit ← `(Unit.unit);
  pure $ Code.jmp ref jp #[unit]
else
  pure $ Code.jmp ref jp (xs.map $ mkIdentFrom ref)

/- Create a new joinpoint that takes `rs` and `val` as arguments. `val` must be syntax representing a pure value.
   The body of the joinpoint is created using `mkJPBody yFresh`, where `yFresh`
   is a fresh variable created by this method. -/
def mkJmp (ref : Syntax) (rs : NameSet) (val : Syntax) (mkJPBody : Syntax → MacroM Code) : StateRefT (Array JPDecl) TermElabM Code := do
let xs := nameSetToArray rs;
let args := xs.map $ mkIdentFrom ref;
let args := args.push val;
yFresh ← mkFreshUserName `y;
let ps := xs.map fun x => (x, true);
let ps := ps.push (yFresh, false);
jpBody ← liftMacroM $ mkJPBody (mkIdentFrom ref yFresh);
jp ← addFreshJP ps jpBody;
pure $ Code.jmp ref jp args

/- `pullExitPointsAux rs c` auxiliary method for `pullExitPoints`, `rs` is the set of update variable in the current path.  -/
partial def pullExitPointsAux : NameSet → Code → StateRefT (Array JPDecl) TermElabM Code
| rs, Code.decl xs stx k         => Code.decl xs stx <$> pullExitPointsAux (eraseVars rs xs) k
| rs, Code.reassign xs stx k     => Code.reassign xs stx <$> pullExitPointsAux (insertVars rs xs) k
| rs, Code.joinpoint j ps b k    => Code.joinpoint j ps <$> pullExitPointsAux rs b <*> pullExitPointsAux rs k
| rs, Code.seq e k               => Code.seq e <$> pullExitPointsAux rs k
| rs, Code.ite ref x? o c t e    => Code.ite ref x? o c <$> pullExitPointsAux (eraseOptVar rs x?) t <*> pullExitPointsAux (eraseOptVar rs x?) e
| rs, Code.«match» ref ds t alts => Code.«match» ref ds t <$> alts.mapM fun alt => do
  rhs ← pullExitPointsAux (eraseVars rs alt.vars) alt.rhs; pure { alt with rhs := rhs }
| rs, c@(Code.jmp _ _ _)         => pure c
| rs, Code.«break» ref           => mkSimpleJmp ref rs (Code.«break» ref)
| rs, Code.«continue» ref        => mkSimpleJmp ref rs (Code.«continue» ref)
| rs, Code.«return» ref val      => mkJmp ref rs val (fun y => pure $ Code.«return» ref y)
| rs, Code.action e              =>
  -- We use `mkAuxDeclFor` because `e` is not pure.
  mkAuxDeclFor e fun y =>
    let ref := e;
    mkJmp ref rs y (fun yFresh => do eNew ← `(HasPure.pure $yFresh); pure $ Code.action eNew)

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
def pullExitPoints (c : Code) : TermElabM Code :=
if hasExitPoint c then do
  (c, jpDecls) ← (pullExitPointsAux {} c).run #[];
  pure $ attachJPs jpDecls c
else
  pure c

partial def extendUpdatedVarsAux (ws : NameSet) : Code → TermElabM Code
| Code.joinpoint j ps b k        => Code.joinpoint j ps <$> extendUpdatedVarsAux b <*> extendUpdatedVarsAux k
| Code.seq e k                   => Code.seq e <$> extendUpdatedVarsAux k
| c@(Code.«match» ref ds t alts) =>
  if alts.any fun alt => alt.vars.any fun x => ws.contains x then
    -- If a pattern variable is shadowing a variable in ws, we `pullExitPoints`
    pullExitPoints c
  else
    Code.«match» ref ds t <$> alts.mapM fun alt => do rhs ← extendUpdatedVarsAux alt.rhs; pure { alt with rhs := rhs }
| Code.ite ref none o c t e =>
  Code.ite ref none o c <$> extendUpdatedVarsAux t <*> extendUpdatedVarsAux e
| c@(Code.ite ref (some h) o cond t e) =>
  if ws.contains h then
    -- if the `h` at `if h:c then t else e` shadows a variable in `ws`, we `pullExitPoints`
    pullExitPoints c
  else
    Code.ite ref (some h) o cond <$> extendUpdatedVarsAux t <*> extendUpdatedVarsAux e
| Code.reassign xs stx k => Code.reassign xs stx <$> extendUpdatedVarsAux k
| c@(Code.decl xs stx k) =>
  if xs.any fun x => ws.contains x then
    -- One the declared variables is shadowing a variable in `ws`
    pullExitPoints c
  else
    Code.decl xs stx <$> extendUpdatedVarsAux k
| c => pure c

/-
Extend the set of updated variables. It assumes `ws` is a super set of `c.uvars`.
We **cannot** simply update the field `c.uvars`, because `c` may have shadowed some variable in `ws`.
See discussion at `pullExitPoints`.
-/
def extendUpdatedVars (c : CodeBlock) (ws : NameSet) : TermElabM CodeBlock :=
if ws.any fun x => !c.uvars.contains x then do
  -- `ws` contains a variable that is not in `c.uvars`, but in `c.dvars` (i.e., it has been shadowed)
  code ← extendUpdatedVarsAux ws c.code;
  pure { code := code, uvars := ws }
else
  pure { c with uvars := ws }

private def union (s₁ s₂ : NameSet) : NameSet :=
s₁.fold (fun (s : NameSet) x => s.insert x) s₂

/-
Given two code blocks `c₁` and `c₂`, make sure they have the same set of updated variables.
Let `ws` the union of the updated variables in `c₁‵ and ‵c₂`.
We use `extendUpdatedVars c₁ ws` and `extendUpdatedVars c₂ ws`
-/
def homogenize (c₁ c₂ : CodeBlock) : TermElabM (CodeBlock × CodeBlock) := do
let ws := union c₁.uvars c₂.uvars;
c₁ ← extendUpdatedVars c₁ ws;
c₂ ← extendUpdatedVars c₂ ws;
pure (c₁, c₂)

/-
Extending code blocks with variable declarations: `let x : t := v` and `let x : t ← v`.
We remove `x` from the collection of updated varibles.
Remark: `stx` is the syntax for the declaration (e.g., `letDecl`), and `xs` are the variables
declared by it. It is an array because we have let-declarations that declare multiple variables.
Example: `let (x, y) := t`
-/
def mkVarDeclCore (xs : Array Name) (stx : Syntax) (c : CodeBlock) : CodeBlock :=
{ code := Code.decl xs stx c.code, uvars := eraseVars c.uvars xs }

/-
Extending code blocks with reassignments: `x : t := v` and `x : t ← v`.
Remark: `stx` is the syntax for the declaration (e.g., `letDecl`), and `xs` are the variables
declared by it. It is an array because we have let-declarations that declare multiple variables.
Example: `(x, y) ← t`
-/
def mkReassignCore (xs : Array Name) (stx : Syntax) (c : CodeBlock) : TermElabM CodeBlock := do
let us := c.uvars;
let ws := insertVars us xs;
-- If `xs` contains a new updated variable, then we must use `extendUpdatedVars`.
-- See discussion at `pullExitPoints`
code ← if xs.any fun x => !us.contains x then extendUpdatedVarsAux ws c.code else pure c.code;
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
let x? := if optIdent.isNone then none else some (optIdent.getArg 0).getId;
(thenBranch, elseBranch) ← homogenize thenBranch elseBranch;
pure {
  code  := Code.ite ref x? optIdent cond thenBranch.code elseBranch.code,
  uvars := thenBranch.uvars,
}

private def mkUnit (ref : Syntax) : MacroM Syntax := do
unit ← `(PUnit.unit);
pure $ unit.copyInfo ref

private def mkPureUnit (ref : Syntax) : MacroM Syntax := do
unit ← mkUnit ref;
pureUnit ← `(HasPure.pure $(unit.copyInfo ref));
pure $ pureUnit.copyInfo ref

def mkPureUnitAction (ref : Syntax) : MacroM CodeBlock := do
mkTerminalAction <$> mkPureUnit ref

def mkUnless (ref : Syntax) (cond : Syntax) (c : CodeBlock) : MacroM CodeBlock := do
thenBranch ← mkPureUnitAction ref;
pure { c with code := Code.ite ref none mkNullNode cond thenBranch.code c.code }

def mkMatch (ref : Syntax) (discrs : Syntax) (optType : Syntax) (alts : Array (Alt CodeBlock)) : TermElabM CodeBlock := do
-- nary version of homogenize
let ws := alts.foldl (fun (ws : NameSet) alt => union ws alt.rhs.uvars) {};
alts : Array (Alt Code) ← alts.mapM fun alt => do {
  rhs ← extendUpdatedVars alt.rhs ws;
  pure { ref := alt.ref, vars := alt.vars, patterns := alt.patterns, rhs := rhs.code : Alt Code }
};
pure { code := Code.«match» ref discrs optType alts, uvars := ws }

/- Return a code block that executes `terminal` and then `k` with the value produced by `terminal`.
   This method assumes `terminal` is a terminal -/
def concat (terminal : CodeBlock) (kRef : Syntax) (y? : Option Name) (k : CodeBlock) : TermElabM CodeBlock := do
unless (hasTerminalAction terminal.code) $
  throwErrorAt kRef "'do' element is unreachable";
(terminal, k) ← homogenize terminal k;
let xs := nameSetToArray k.uvars;
y ← match y? with | some y => pure y | none => mkFreshUserName `y;
let ps := xs.map fun x => (x, true);
let ps := ps.push (y, false);
jpDecl ← mkFreshJP ps k.code;
let jp := jpDecl.name;
terminal ← liftMacroM $ convertTerminalActionIntoJmp terminal.code jp xs;
pure { code  := attachJP jpDecl terminal, uvars := k.uvars }

def getLetIdDeclVar (letIdDecl : Syntax) : Name :=
(letIdDecl.getArg 0).getId

def getLetPatDeclVars (letPatDecl : Syntax) : TermElabM (Array Name) := do
let pattern := letPatDecl.getArg 0;
patternVars ← getPatternVars pattern;
pure $ patternVars.filterMap fun patternVar => match patternVar with
  | PatternVar.localVar x => some x
  | _ => none

def getLetEqnsDeclVar (letEqnsDecl : Syntax) : Name :=
(letEqnsDecl.getArg 0).getId

def getLetDeclVars (letDecl : Syntax) : TermElabM (Array Name) := do
let arg := letDecl.getArg 0;
if arg.getKind == `Lean.Parser.Term.letIdDecl then
  pure #[getLetIdDeclVar arg]
else if arg.getKind == `Lean.Parser.Term.letPatDecl then
  getLetPatDeclVars arg
else if arg.getKind == `Lean.Parser.Term.letEqnsDecl then
  pure #[getLetEqnsDeclVar arg]
else
  throwError "unexpected kind of let declaration"

def getDoLetVars (doLet : Syntax) : TermElabM (Array Name) :=
-- parser! "let " >> letDecl
getLetDeclVars (doLet.getArg 1)

def getDoLetRecVars (doLetRec : Syntax) : TermElabM (Array Name) := do
-- letRecDecls is an array of `(group (optional attributes >> letDecl))`
let letRecDecls := (doLetRec.getArg 1).getArgs.getSepElems;
let letDecls := letRecDecls.map fun p => p.getArg 1;
letDecls.foldlM
  (fun allVars letDecl => do
    vars ← getLetDeclVars letDecl;
    pure (allVars ++ vars))
  #[]

-- ident >> optType >> leftArrow >> termParser
def getDoIdDeclVar (doIdDecl : Syntax) : Name :=
(doIdDecl.getArg 0).getId

def getPatternVarNames (pvars : Array PatternVar) : Array Name :=
pvars.filterMap fun pvar => match pvar with
  | PatternVar.localVar x => some x
  | _ => none

-- termParser >> leftArrow >> termParser >> optional (" | " >> termParser)
def getDoPatDeclVars (doPatDecl : Syntax) : TermElabM (Array Name) := do
let pattern := doPatDecl.getArg 0;
patternVars ← getPatternVars pattern;
pure $ getPatternVarNames patternVars

-- parser! "let " >> (doIdDecl <|> doPatDecl)
def getDoLetArrowVars (doLetArrow : Syntax) : TermElabM (Array Name) := do
let decl := doLetArrow.getArg 1;
if decl.getKind == `Lean.Parser.Term.doIdDecl then
  pure #[getDoIdDeclVar decl]
else if decl.getKind == `Lean.Parser.Term.doPatDecl then
  getDoPatDeclVars decl
else
  throwError "unexpected kind of 'do' declaration"

def getDoReassignVars (doReassign : Syntax) : TermElabM (Array Name) := do
let arg := doReassign.getArg 0;
if arg.getKind == `Lean.Parser.Term.letIdDecl then
  pure #[getLetIdDeclVar arg]
else if arg.getKind == `Lean.Parser.Term.letPatDecl then
  getLetPatDeclVars arg
else
  throwError "unexpected kind of reassignment"

def mkDoSeq (doElems : Array Syntax) : Syntax :=
mkNode `Lean.Parser.Term.doSeqIndent #[mkNullNode $ doElems.map fun doElem => mkNullNode #[doElem, mkNullNode]]

def mkSingletonDoSeq (doElem : Syntax) : Syntax :=
mkDoSeq #[doElem]

/-
  Recall that the `doIf` syntax is of the form
  ```
  "if " >> optIdent >> termParser >> " then " >> doSeq
  >> many (group (" else " >> " if ") >> optIdent >> termParser >> " then " >> doSeq)
  >> optional (" else " >> doSeq)
  ```

  Given a `doIf`, return an equivalente `doIf` that has no `else if`s and the `else` is not none.  -/
private def expandDoIf (doIf : Syntax) : MacroM Syntax :=
let ref       := doIf;
let doElseIfs := (doIf.getArg 5).getArgs;
let doElse    := doIf.getArg 6;
if doElseIfs.isEmpty && !doElse.isNone then
  pure doIf
else do
  doElse ←
    if doElse.isNone then do
      pureUnit ← mkPureUnit ref;
      pure $ mkNullNode #[
        mkAtomFrom ref "else",
        mkSingletonDoSeq (mkNode `Lean.Parser.Term.doExpr #[pureUnit])
      ]
    else
      pure $ doElse;
  let doElse := doElseIfs.foldr
    (fun doElseIf doElse =>
      let ifAtom := (doElseIf.getArg 0).getArg 1;
      let doIfArgs := (doElseIf.getArgs).set! 0 ifAtom;
      let doIfArgs := doIfArgs.push mkNullNode;
      let doIfArgs := doIfArgs.push doElse;
      mkNullNode #[mkAtomFrom doElseIf "else",
                   mkSingletonDoSeq $ mkNode `Lean.Parser.Term.doIf doIfArgs])
    doElse;
  let doIf := doIf.setArg 6 doElse;
  pure $ doIf.setArg 5 mkNullNode -- remove else-ifs

structure DoIfView :=
(ref        : Syntax)
(optIdent   : Syntax)
(cond       : Syntax)
(thenBranch : Syntax)
(elseBranch : Syntax)

private def mkDoIfView (doIf : Syntax) : MacroM DoIfView := do
doIf ← expandDoIf doIf;
pure {
  ref        := doIf,
  optIdent   := doIf.getArg 1,
  cond       := doIf.getArg 2,
  thenBranch := doIf.getArg 4,
  elseBranch := (doIf.getArg 6).getArg 1 }

private def mkTuple (ref : Syntax) (elems : Array Syntax) : MacroM Syntax :=
if elems.size == 0 then do
  mkUnit ref
else if elems.size == 1 then
  pure (elems.get! 0)
else
  (elems.extract 0 (elems.size - 1)).foldrM
    (fun elem tuple => do
      tuple ← `(($elem, $tuple));
      pure $ tuple.copyInfo ref)
    (elems.back)

/- Return `some action` if `doElem` is a `doExpr <action>`-/
def isDoExpr? (doElem : Syntax) : Option Syntax :=
if doElem.getKind == `Lean.Parser.Term.doExpr then
  some $ doElem.getArg 0
else
  none

-- Code block to syntax term
namespace ToTerm

inductive Kind
| regular
| forInNestedTerm
| forIn
| forInWithReturn

def Kind.isRegular : Kind → Bool
| Kind.regular => true
| _            => false

structure Context :=
(m     : Syntax) -- Syntax to reference the monad associated with the do notation.
(uvars : Array Name)
(kind  : Kind)

abbrev M := ReaderT Context MacroM

def mkUVarTuple (ref : Syntax) : M Syntax := do
ctx ← read;
let uvarIdents := ctx.uvars.map fun x => mkIdentFrom ref x;
liftM $ mkTuple ref uvarIdents

def returnToTermCore (ref : Syntax) (val : Syntax) : M Syntax := do
ctx ← read;
u ← mkUVarTuple ref;
match ctx.kind with
| Kind.regular         => if ctx.uvars.isEmpty then `(HasPure.pure $val) else `(HasPure.pure ($val, $u))
| Kind.forInNestedTerm => `(HasPure.pure (DoResult.«return» $val $u))
| Kind.forIn           => `(HasPure.pure (ForInStep.done $u))
| Kind.forInWithReturn => `(HasPure.pure (ForInStep.done (some $val, $u)))

def returnToTerm (ref : Syntax) (val : Syntax) : M Syntax := do
r ← returnToTermCore ref val;
pure $ r.copyInfo ref

def continueToTermCore (ref : Syntax) : M Syntax := do
ctx ← read;
u ← mkUVarTuple ref;
match ctx.kind with
| Kind.regular         => unreachable!
| Kind.forInNestedTerm => `(HasPure.pure (DoResult.«continue» $u))
| Kind.forIn           => `(HasPure.pure (ForInStep.yield $u))
| Kind.forInWithReturn => `(HasPure.pure (ForInStep.yield (none, $u)))

def continueToTerm (ref : Syntax) : M Syntax := do
r ← continueToTermCore ref;
pure $ r.copyInfo ref

def breakToTermCore (ref : Syntax) : M Syntax := do
ctx ← read;
u ← mkUVarTuple ref;
match ctx.kind with
| Kind.regular         => unreachable!
| Kind.forInNestedTerm => `(HasPure.pure (DoResult.«break» $u))
| Kind.forInWithReturn => `(HasPure.pure (ForInStep.done (none, $u)))
| Kind.forIn           => `(HasPure.pure (ForInStep.done $u))

def breakToTerm (ref : Syntax) : M Syntax := do
r ← breakToTermCore ref;
pure $ r.copyInfo ref

def actionTerminalToTermCore (action : Syntax) : M Syntax := withFreshMacroScope do
let ref := action;
ctx ← read;
u ← mkUVarTuple ref;
match ctx.kind with
| Kind.forInNestedTerm => `(HasBind.bind $action fun y => (HasPure.pure (DoResult.«pure» y $u)))
| Kind.forIn           => `(HasBind.bind $action fun _ => HasPure.pure (ForInStep.yield $u))
| Kind.forInWithReturn => `(HasBind.bind $action fun _ => HasPure.pure (ForInStep.yield (none, $u)))
| Kind.regular         => if ctx.uvars.isEmpty then pure action else `(HasBind.bind $action fun y => HasPure.pure (y, $u))

def actionTerminalToTerm (action : Syntax) : M Syntax := do
let ref := action;
r ← actionTerminalToTermCore action;
pure $ r.copyInfo ref

def seqToTermCore (action : Syntax) (k : Syntax) : MacroM Syntax := withFreshMacroScope do
if action.getKind == `Lean.Parser.Term.doDbgTrace then
  let msg := action.getArg 1;
  `(dbgTrace! $msg; $k)
else if action.getKind == `Lean.Parser.Term.doAssert then
  let cond := action.getArg 1;
  `(assert! $cond; $k)
else do
  `(HasBind.bind $action (fun _ => $k))

def seqToTerm (action : Syntax) (k : Syntax) : MacroM Syntax := do
r ← seqToTermCore action k;
pure $ r.copyInfo action

def declToTermCore (decl : Syntax) (k : Syntax) : M Syntax := withFreshMacroScope do
let kind := decl.getKind;
if kind == `Lean.Parser.Term.doLet then
  let letDecl := decl.getArg 1;
  `(let $letDecl:letDecl; $k)
else if kind == `Lean.Parser.Term.doLetRec then
  let letRecToken := decl.getArg 0;
  let letRecDecls := decl.getArg 1;
  pure $ mkNode `Lean.Parser.Term.letrec #[letRecToken, letRecDecls, mkNullNode, k]
else if kind == `Lean.Parser.Term.doLetArrow then
  let arg := decl.getArg 1;
  let ref := arg;
  if arg.getKind == `Lean.Parser.Term.doIdDecl then
    let id     := arg.getArg 0;
    let type   := expandOptType ref (arg.getArg 1);
    let doElem := arg.getArg 3;
    -- `doElem` must be a `doExpr action`. See `doLetArrowToCode`
    match isDoExpr? doElem with
    | some action => `(HasBind.bind $action (fun ($id:ident : $type) => $k))
    | none        => liftM $ Macro.throwError decl "unexpected kind of 'do' declaration"
  else
    liftM $ Macro.throwError decl "unexpected kind of 'do' declaration"
else if kind == `Lean.Parser.Term.doHave then
  liftM $ Macro.throwError decl ("WIP " ++ toString decl)
else
  liftM $ Macro.throwError decl "unexpected kind of 'do' declaration"

def declToTerm (decl : Syntax) (k : Syntax) : M Syntax := do
r ← declToTermCore decl k;
pure $ r.copyInfo decl

def reassignToTermCore (reassign : Syntax) (k : Syntax) : MacroM Syntax := withFreshMacroScope do
let kind := reassign.getKind;
if kind == `Lean.Parser.Term.doReassign then
  -- doReassign := parser! (letIdDecl <|> letPatDecl)
  let arg := reassign.getArg 0;
  if arg.getKind == `Lean.Parser.Term.letIdDecl then do
    -- letIdDecl := parser! ident >> many (ppSpace >> bracketedBinder) >> optType >>  " := " >> termParser
    let x   := arg.getArg 0;
    let val := arg.getArg 4;
    newVal ← `(ensureTypeOf! $x $(quote "invalid reassignment, value") $val);
    let arg := arg.setArg 4 newVal;
    let letDecl := mkNode `Lean.Parser.Term.letDecl #[arg];
    `(let $letDecl:letDecl; $k)
  else
    -- TODO: ensure the types did not change
    let letDecl := mkNode `Lean.Parser.Term.letDecl #[arg];
    `(let $letDecl:letDecl; $k)
else if kind == `Lean.Parser.Term.doReassignArrow then
  Macro.throwError reassign ("WIP " ++ toString reassign)
else
  Macro.throwError reassign "unexpected kind of 'do' reassignment"

def reassignToTerm (reassign : Syntax) (k : Syntax) : MacroM Syntax := do
r ← reassignToTermCore reassign k;
pure $ r.copyInfo reassign

def mkIte (ref : Syntax) (optIdent : Syntax) (cond : Syntax) (thenBranch : Syntax) (elseBranch : Syntax) : Syntax :=
mkNode `Lean.Parser.Term.«if» #[mkAtomFrom ref "if", optIdent, cond, mkAtomFrom ref "then", thenBranch, mkAtomFrom ref "else", elseBranch]

def mkJoinPointCore (j : Name) (ps : Array (Name × Bool)) (body : Syntax) (k : Syntax) : M Syntax := withFreshMacroScope do
let ref := body;
binders ← ps.mapM fun ⟨id, useTypeOf⟩ => do {
  type ← if useTypeOf then `(typeOf! $(mkIdentFrom ref id)) else `(_);
  let binderType := mkNullNode #[mkAtomFrom ref ":", type];
  pure $ mkNode `Lean.Parser.Term.explicitBinder #[mkAtomFrom ref "(", mkNullNode #[mkIdentFrom ref id], binderType, mkNullNode, mkAtomFrom ref ")"]
};
ctx ← read;
let m := ctx.m;
type ← `($m _);
/-
We use `let*` instead of `let` for joinpoints to make sure `$k` is elaborated before `$body`.
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
If we use the regular `let` instead of `let*`, the joinpoint `jp` will be elaborated and its type will be inferred to be `Unit → IO (IO.Ref Bool)`.
Then, we get a typing error at `jp ()`. By using `let*`, we first elaborate `if x > 0 ...` and learn that `jp` has type `Unit → IO Unit`.
Then, we get the expected type mismatch error at `IO.mkRef true`. -/
`(let* $(mkIdentFrom ref j):ident $binders:explicitBinder* : $type := $body; $k)

def mkJoinPoint (j : Name) (ps : Array (Name × Bool)) (body : Syntax) (k : Syntax) : M Syntax := do
r ← mkJoinPointCore j ps body k;
pure $ r.copyInfo body

def mkJmp (ref : Syntax) (j : Name) (args : Array Syntax) : Syntax :=
mkAppStx (mkIdentFrom ref j) args

partial def toTerm : Code → M Syntax
| Code.«return» ref val   => returnToTerm ref val
| Code.«continue» ref     => continueToTerm ref
| Code.«break» ref        => breakToTerm ref
| Code.action e           => actionTerminalToTerm e
| Code.joinpoint j ps b k => do b ← toTerm b; k ← toTerm k; mkJoinPoint j ps b k
| Code.jmp ref j args     => pure $ mkJmp ref j args
| Code.decl _ stx k       => do k ← toTerm k; declToTerm stx k
| Code.reassign _ stx k   => do k ← toTerm k; liftM $ reassignToTerm stx k
| Code.seq stx k          => do k ← toTerm k; liftM $ seqToTerm stx k
| Code.ite ref _ o c t e  => do t ← toTerm t; e ← toTerm e; pure $ mkIte ref o c t e
| Code.«match» ref discrs optType alts => do
  termSepAlts : Array Syntax ← alts.foldlM
    (fun (termAlts : Array Syntax) alt => do
      let termAlts := termAlts.push $ mkAtomFrom alt.ref "|";
      rhs ← toTerm alt.rhs;
      let termAlt  := mkNode `Lean.Parser.Term.matchAlt #[alt.patterns, mkAtomFrom alt.ref "=>", rhs];
      let termAlts := termAlts.push termAlt;
      pure termAlts)
    #[];
  let firstVBar     := termSepAlts.get! 0;
  let termSepAlts   := mkNullNode $ termSepAlts.extract 1 termSepAlts.size;
  let termMatchAlts := mkNode `Lean.Parser.Term.matchAlts #[mkNullNode #[firstVBar], termSepAlts];
  pure $ mkNode `Lean.Parser.Term.«match» #[mkAtomFrom ref "match", discrs, optType, mkAtomFrom ref "with", termMatchAlts]

def run (code : Code) (m : Syntax) (uvars : Array Name := #[]) (kind := Kind.regular) : MacroM Syntax := do
term ← toTerm code { m := m, kind := kind, uvars := uvars };
pure term

end ToTerm

namespace ToCodeBlock

structure Context :=
(ref       : Syntax)
(m         : Syntax) -- Syntax representing the monad associated with the do notation.
(varSet    : NameSet := {})
(insideFor : Bool := false)

abbrev M := ReaderT Context TermElabM

@[inline] def withNewVars {α} (newVars : Array Name) (x : M α) : M α :=
adaptReader (fun (ctx : Context) => { ctx with varSet := insertVars ctx.varSet newVars }) x

def checkReassignable (xs : Array Name) : M Unit := do
ctx ← read;
xs.forM fun x =>
  unless (ctx.varSet.contains x) do
    r? ← liftM $ resolveLocalName x;
    match r? with
    | some (_, []) => pure ()
    | _ => throwError ("'" ++ x.simpMacroScopes ++ "' cannot be reassigned")

@[inline] def withFor {α} (x : M α) : M α :=
adaptReader (fun (ctx : Context) => { ctx with insideFor := true }) x

structure ToForInTermResult :=
(uvars      : Array Name)
(term       : Syntax)

def mkForInBody  (x : Syntax) (forInBody : CodeBlock) : M ToForInTermResult := do
ctx ← read;
let uvars     := forInBody.uvars;
let uvars     := nameSetToArray uvars;
term ← liftMacroM $ ToTerm.run forInBody.code ctx.m uvars (if hasReturn forInBody.code then ToTerm.Kind.forInWithReturn else ToTerm.Kind.forIn);
pure ⟨uvars, term⟩

def ensureInsideFor : M Unit := do
ctx ← read;
unless ctx.insideFor $
  throwError "invalid 'do' element, it must be inside 'for'"

def ensureEOS (doElems : List Syntax) : M Unit :=
unless doElems.isEmpty $
  throwError "must be last element in a 'do' sequence"

private partial def expandLiftMethodAux : Syntax → StateT (List Syntax) MacroM Syntax
| stx@(Syntax.node k args) =>
  if k == `Lean.Parser.Term.do then pure stx
  else if k == `Lean.Parser.Term.doSeqIndent then pure stx
  else if k == `Lean.Parser.Term.doSeqBracketed then pure stx
  else if k == `Lean.Parser.Term.quot then pure stx
  else if k == `Lean.Parser.Term.liftMethod then withFreshMacroScope $ do
    let term := args.get! 1;
    term ← expandLiftMethodAux term;
    auxDo ← `(do let a ← $term:term);
    let auxDoElems := getDoSeqElems (getDoSeq auxDo);
    modify fun s => s ++ auxDoElems;
    `(a)
  else do
    args ← args.mapM expandLiftMethodAux;
    pure $ Syntax.node k args
| stx => pure stx

def expandLiftMethod (doElem : Syntax) : MacroM (List Syntax × Syntax) :=
if !hasLiftMethod doElem then pure ([], doElem)
else do
  (doElem, doElemsNew) ← (expandLiftMethodAux doElem).run [];
  pure (doElemsNew, doElem)

/- "Concatenate" `c` with `doSeqToCode doElems` -/
def concatWith (doSeqToCode : List Syntax → M CodeBlock) (c : CodeBlock) (doElems : List Syntax) : M CodeBlock :=
match doElems with
| [] => pure c
| nextDoElem :: _  => do
  k ← doSeqToCode doElems;
  let ref := nextDoElem;
  liftM $ concat c ref none k

def checkLetArrowRHS (doElem : Syntax) : M Unit :=
let kind := doElem.getKind;
when (kind == `Lean.Parser.Term.doLetArrow ||
      kind == `Lean.Parser.Term.doLet ||
      kind == `Lean.Parser.Term.doLetRec ||
      kind == `Lean.Parser.Term.doHave ||
      kind == `Lean.Parser.Term.doReassign ||
      kind == `Lean.Parser.Term.doReassignArrow) do
  throwErrorAt doElem "invalid kind of value in an assignment"

/- Generate `CodeBlock` for `doLetArrow; doElems`
   `doLetArrow` is of the form
   ```
   "let " >> (doIdDecl <|> doPatDecl)
   ```
   where
   ```
   def doIdDecl   := parser! ident >> optType >> leftArrow >> doElemParser
   def doPatDecl  := parser! termParser >> leftArrow >> doElemParser >> optional (" | " >> doElemParser)
   ``` -/
def doLetArrowToCode (doSeqToCode : List Syntax → M CodeBlock) (doLetArrow : Syntax) (doElems : List Syntax) : M CodeBlock := do
let ref  := doLetArrow;
let decl := doLetArrow.getArg 1;
if decl.getKind == `Lean.Parser.Term.doIdDecl then
  let doElem := decl.getArg 3;
  match isDoExpr? doElem with
  | some action =>
    let var := getDoIdDeclVar decl;
    mkVarDeclCore #[var] doLetArrow <$> withNewVars #[var] (doSeqToCode doElems)
  | none => do
    checkLetArrowRHS doElem;
    match doElems with
    | [] => doSeqToCode [doElem]
    | kRef::_  => do
      let y := decl.getIdAt 0;
      c ← doSeqToCode [doElem];
      k ← withNewVars #[y] $ doSeqToCode doElems;
      liftM $ concat c kRef y k
else if decl.getKind == `Lean.Parser.Term.doPatDecl then
  let pattern := decl.getArg 0;
  let doElem  := decl.getArg 2;
  let optElse := decl.getArg 3;
  if optElse.isNone then withFreshMacroScope do
    auxDo ← `(do let discr ← $doElem; let $pattern:term := discr);
    doSeqToCode $ getDoSeqElems (getDoSeq auxDo) ++ doElems
  else do
    let contSeq := mkDoSeq doElems.toArray;
    let elseSeq := mkSingletonDoSeq (optElse.getArg 1);
    auxDo ← `(do let discr ← $doElem; match discr with | $pattern:term => $contSeq | _ => $elseSeq);
    doSeqToCode $ getDoSeqElems (getDoSeq auxDo)
else
  throwError "unexpected kind of 'do' declaration"

/- Generate `CodeBlock` for `doIf; doElems`
   `doIf` is of the form
   ```
   "if " >> optIdent >> termParser >> " then " >> doSeq
    >> many (group (try (group (" else " >> " if ")) >> optIdent >> termParser >> " then " >> doSeq))
    >> optional (" else " >> doSeq)
   ```  -/
def doIfToCode (doSeqToCode : List Syntax → M CodeBlock) (doIf : Syntax) (doElems : List Syntax) : M CodeBlock := do
view ← liftMacroM $ mkDoIfView doIf;
thenBranch ← doSeqToCode (getDoSeqElems view.thenBranch);
elseBranch ← doSeqToCode (getDoSeqElems view.elseBranch);
ite ← liftM $ mkIte view.ref view.optIdent view.cond thenBranch elseBranch;
concatWith doSeqToCode ite doElems

/- Generate `CodeBlock` for `doUnless; doElems`
   `doUnless` is of the form
   ```
   "unless " >> termParser >> "do " >> doSeq
   ```  -/
def doUnlessToCode (doSeqToCode : List Syntax → M CodeBlock) (doUnless : Syntax) (doElems : List Syntax) : M CodeBlock := do
let ref   := doUnless;
let cond  := doUnless.getArg 1;
let doSeq := doUnless.getArg 3;
body ← doSeqToCode (getDoSeqElems doSeq);
unlessCode ← liftMacroM $ mkUnless ref cond body;
concatWith doSeqToCode unlessCode doElems

/- Generate `CodeBlock` for `doFor; doElems`
   `doFor` is of the form
   ```
   for " >> termParser >> " in " >> termParser >> "do " >> doSeq
   ``` -/
def doForToCode (doSeqToCode : List Syntax → M CodeBlock) (doFor : Syntax) (doElems : List Syntax) : M CodeBlock := do
let ref       := doFor;
let x         := doFor.getArg 1;
let xs        := doFor.getArg 3;
let forElems  := getDoSeqElems (doFor.getArg 5);
let newVars   := if x.isIdent then #[x.getId] else #[];
forInBodyCodeBlock  ← withNewVars newVars $ withFor (doSeqToCode forElems);
-- trace! `Elab.do forInBodyCodeBlock.toMessageData;
⟨uvars, forInBody⟩ ← mkForInBody x forInBodyCodeBlock;
uvarsTuple ← liftMacroM $ mkTuple ref (uvars.map (mkIdentFrom ref));
if hasReturn forInBodyCodeBlock.code then do
  forInTerm ← `($(xs).forIn (none, $uvarsTuple) fun $x (_, $uvarsTuple) => $forInBody);
  auxDo ← `(do let r ← $forInTerm:term; $uvarsTuple:term := r.2; match r.1 with | none => HasPure.pure (ensureExpectedType! "type mismatch, 'for'" PUnit.unit) | some a => return ensureExpectedType! "type mismatch, 'for'" a);
  doSeqToCode (getDoSeqElems (getDoSeq auxDo) ++ doElems)
else do
  forInTerm ← `($(xs).forIn $uvarsTuple fun $x $uvarsTuple => $forInBody);
  if doElems.isEmpty then do
    auxDo ← `(do let r ← $forInTerm:term; $uvarsTuple:term := r; HasPure.pure (ensureExpectedType! "type mismatch, 'for'" PUnit.unit));
    doSeqToCode $ getDoSeqElems (getDoSeq auxDo)
  else do
    auxDo ← `(do let r ← $forInTerm:term; $uvarsTuple:term := r);
    doSeqToCode (getDoSeqElems (getDoSeq auxDo) ++ doElems)

/--
  Generate `CodeBlock` for `doMatch; doElems`
  ```
  def doMatchAlt   := sepBy1 termParser ", " >> darrow >> doSeq
  def doMatchAlts  := parser! optional "| " >> sepBy1 doMatchAlt "|"
  def doMatch      := parser! "match " >> sepBy1 matchDiscr ", " >> optType >> " with " >> doMatchAlts
  ``` -/
def doMatchToCode (doSeqToCode : List Syntax → M CodeBlock) (doMatch : Syntax) (doElems: List Syntax) : M CodeBlock := do
let ref       := doMatch;
let discrs    := doMatch.getArg 1;
let optType   := doMatch.getArg 2;
let matchAlts := ((doMatch.getArg 4).getArg 1).getArgs.getSepElems; -- Array of `doMatchAlt`
alts : Array (Alt CodeBlock) ←  matchAlts.mapM fun matchAlt => do {
  let patterns := matchAlt.getArg 0;
  pvars ← liftM $ getPatternsVars patterns.getArgs.getSepElems;
  let vars := getPatternVarNames pvars;
  let rhs  := matchAlt.getArg 2;
  rhs ← withNewVars vars $ doSeqToCode (getDoSeqElems rhs);
  pure { ref := matchAlt, vars := vars, patterns := patterns, rhs := rhs : Alt CodeBlock }
};
matchCode ← liftM $ mkMatch ref discrs optType alts;
concatWith doSeqToCode matchCode doElems

/- Generate `CodeBlock` for `doReturn` which is of the form
   ```
   "return " >> optional termParser
   ```
   `doElems` is only used for sanity checking. -/
def doReturnToCode (doReturn : Syntax) (doElems: List Syntax) : M CodeBlock := do
let ref := doReturn;
ensureEOS doElems;
let argOpt := doReturn.getArg 1;
arg ← if argOpt.isNone then liftMacroM $ mkUnit ref else pure $ argOpt.getArg 0;
pure $ mkReturn ref arg

partial def doSeqToCode : List Syntax → M CodeBlock
| [] => do ctx ← read; liftMacroM $ mkPureUnitAction ctx.ref
| doElem::doElems => withRef doElem do
  (liftedDoElems, doElem) ← liftM (liftMacroM $ expandLiftMethod doElem : TermElabM _);
  if !liftedDoElems.isEmpty then
    doSeqToCode (liftedDoElems ++ [doElem] ++ doElems)
  else do
    let ref := doElem;
    let concatWithRest (c : CodeBlock) : M CodeBlock := concatWith doSeqToCode c doElems;
    let k := doElem.getKind;
    if k == `Lean.Parser.Term.doLet then do
      vars ← liftM $ getDoLetVars doElem;
      mkVarDeclCore vars doElem <$> withNewVars vars (doSeqToCode doElems)
    else if k == `Lean.Parser.Term.doLetRec then do
      vars ← liftM $ getDoLetRecVars doElem;
      mkVarDeclCore vars doElem <$> withNewVars vars (doSeqToCode doElems)
    else if k == `Lean.Parser.Term.doReassign then do
      vars ← liftM $ getDoReassignVars doElem;
      checkReassignable vars;
      k ← doSeqToCode doElems;
      liftM $ mkReassignCore vars doElem k
    else if k == `Lean.Parser.Term.doLetArrow then do
      doLetArrowToCode doSeqToCode doElem doElems
    else if k == `Lean.Parser.Term.doReassignArrow then
      throwError "WIP"
    else if k == `Lean.Parser.Term.doHave then
      throwError "WIP"
    else if k == `Lean.Parser.Term.doIf then
      doIfToCode doSeqToCode doElem doElems
    else if k == `Lean.Parser.Term.doUnless then do
      doUnlessToCode doSeqToCode doElem doElems
    else if k == `Lean.Parser.Term.doFor then withFreshMacroScope do
      doForToCode doSeqToCode doElem doElems
    else if k == `Lean.Parser.Term.doMatch then do
      doMatchToCode doSeqToCode doElem doElems
    else if k == `Lean.Parser.Term.doTry then
      throwError "WIP"
    else if k == `Lean.Parser.Term.doBreak then do
      ensureInsideFor;
      ensureEOS doElems;
      pure $ mkBreak ref
    else if k == `Lean.Parser.Term.doContinue then do
      ensureInsideFor;
      ensureEOS doElems;
      pure $ mkContinue ref
    else if k == `Lean.Parser.Term.doReturn then
      doReturnToCode doElem doElems
    else if k == `Lean.Parser.Term.doDbgTrace then
      mkSeq doElem <$> doSeqToCode doElems
    else if k == `Lean.Parser.Term.doAssert then
      mkSeq doElem <$> doSeqToCode doElems
    else if k == `Lean.Parser.Term.doExpr then
      let term := doElem.getArg 0;
      if doElems.isEmpty then
        pure $ mkTerminalAction term
      else
        mkSeq term <$> doSeqToCode doElems
    else
      throwError ("unexpected do-element" ++ Format.line ++ toString doElem)

def run (doStx : Syntax) (m : Syntax) : TermElabM CodeBlock :=
(doSeqToCode $ getDoSeqElems $ getDoSeq doStx).run { ref := doStx, m := m }

end ToCodeBlock

/- Create a synthetic metavariable `?m` and assign `m` to it.
   We use `?m` to refer to `m` when expanding the `do` notation. -/
private def mkMonadAlias (m : Expr) : TermElabM Syntax := do
result ← `(?m);
mType ← inferType m;
mvar ← elabTerm result mType;
assignExprMVar mvar.mvarId! m;
pure result

@[builtinTermElab «do»]
def elabDo : TermElab :=
fun stx expectedType? => do
  tryPostponeIfNoneOrMVar expectedType?;
  bindInfo ← extractBind expectedType?;
  m ← mkMonadAlias bindInfo.m;
  codeBlock ← ToCodeBlock.run stx m;
  -- trace! `Elab.do ("codeBlock: " ++ Format.line ++ codeBlock.toMessageData);
  stxNew ← liftMacroM $ ToTerm.run codeBlock.code m;
  trace! `Elab.do stxNew;
  let expectedType := mkApp bindInfo.m bindInfo.α;
  withMacroExpansion stx stxNew $ elabTermEnsuringType stxNew expectedType

end Do

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab.do;
pure ()

end Term
end Elab
end Lean
