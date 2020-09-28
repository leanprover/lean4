/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Term
import Lean.Elab.Binders
import Lean.Elab.Quotation

namespace Lean
namespace Elab
namespace Term

open Meta

namespace Do

structure Alt (σ : Type) :=
(ref : Syntax) (patterns : Array Syntax) (rhs : σ)

/-
  Auxiliary datastructure for representing a `do` code block.
  We convert `Code` into a `Syntax` term representing the:
  - `do`-block, or
  - the visitor argument for the `forIn` combinator.

  We have 2 kinds of declaration
  - `vdecl`: variable declaration
  - `jdecl`: join-point declaration

  and actions (e.g., `IO.println "hello"`)
  - `action`

  We have 6 terminals
  - `break`:    for interrupting a `for x in s`
  - `continue`: for interrupting the current iteration of a `for x in s`
  - `return`:   returning the result of the computation.
  - `ite`:      if-then-else
  - `match`:    pattern matching
  - `jmp`       a goto to a join-point

  We store the set of updated variables `uvars` in the terminals `break`, `continue`, and `return`.
  The terminal `return` also contains the name of the variable containing the result of the computation.
  We ignore this value when inside a `for x in s`.

  A code block `C` is well-formed if
  1- The collection of updated variables is the same in all `break`
     `continue` and `return` in `C`.

  2- For every `jmp r j as` in `C`, there is a `jdecl r j ps b k` s.t. `jmp r j` is in `k`, and
     `ps.size == as.size`

  3- The update variables occurring in `break`, `continue`, and `return` are pairwise distinct.

  We use the notation `C[u_1, ..., u_k]` to denote a code block that updates variables `u_1, ..., u_k`

-/
inductive Code
| vdecl      (ref : Syntax) (id : Name) (type : Syntax) (pure : Bool) (val : Syntax) (cont : Code)
| jdecl      (ref : Syntax) (id : Name) (params : Array Name) (body : Code) (cont : Code)
| action     (term : Syntax) (cond : Code)
| «break»    (ref : Syntax) (uvars : Array Name)
| «continue» (ref : Syntax) (uvars : Array Name)
| «return»   (ref : Syntax) (var? : Option Name) (uvars : Array Name)
| ite        (ref : Syntax) (cond : Syntax) (thenBranch : Code) (elseBranch : Code)
| «match»    (ref : Syntax) (discrs : Array Syntax) (type? : Option Syntax) (alts : Array (Alt Code))
| jmp        (ref : Syntax) (jpName : Name) (args : Array Name)

instance body.inhabited : Inhabited Code :=
⟨Code.«break» (arbitrary _) #[]⟩

instance alt.inhabited : Inhabited (Alt Code) :=
⟨{ ref := arbitrary _, patterns := #[], rhs := arbitrary _ }⟩

partial def getUpdatedVars? : Code → Option (Array Name)
| Code.vdecl _ _ _ _ _ k   => getUpdatedVars? k
| Code.jdecl _ _ _ b k     => getUpdatedVars? b <|> getUpdatedVars? k
| Code.action _ k          => getUpdatedVars? k
| Code.«break»  _ uvars    => some uvars
| Code.«continue»  _ uvars => some uvars
| Code.«return» _ _ uvars  => some uvars
| Code.ite _ _ t e         => getUpdatedVars? t <|> getUpdatedVars? e
| Code.«match» _ _ _ alts  => alts.findSome? fun alt => getUpdatedVars? alt.rhs
| Code.jmp _ _ _           => none

private def mkTuple (elems : Array Syntax) : MacroM Syntax :=
if elems.size == 1 then pure (elems.get! 0)
else
  (elems.extract 0 (elems.size - 1)).foldrM
    (fun elem tuple => `(($elem, $tuple)))
    (elems.back)

/-
Extending code blocks with variable declarations: `let x : t := v` and `let x : t ← v`.

Suppose we have a code block `C[us]`, and we want to extend it with the
`let x : t := v` declaration. We first remove `x` from the collection of updated variables `us`, obtaining `us'`
and return:
```
Code.vdecl _ x t true v C[us']
```
The operation is the same for `let x : t ← v`, but we set `pure` with `false`.
-/

/-
Extending code blocks with reassignments: `x : t := v` and `x : t ← v`.

Suppose we have a code block `C[us]`, and we want to extend it with the
`x : t := v` reassignment. If `x` is in `us`, then we just return
```
Code.vdecl _ x t true v C[us]
```
If `x` is not in `us`, we create a C'[x, us] in the following way
1- for each `return _ y us` occurring in `C[us]`, we create a join point
  `let j (y us) := return y [x, us]`
  and we replace the `return _ y us` with `jmp y us`
2- for each `break us` occurring in `C[us]`, we create a join point
  `let j (us) := break [x, us]`
  and we replace the `break us` with `jmp us`.
3- Same as 2 for `continue us`
Finally, we return
```
Code.vdecl _ x t true v C'[x, us]
```

Note that it would be incorrect to just add `x` to the set of updated variables of each `break`, `continue`, and `return`.
The problem is that `C` may have shadowed `x`. As an example, consider the following piece of code
```
let x ← action₁; -- declares 'x'
x := x + 1;      -- reassigns 'x'
IO.println x;
let x ← action₂; -- shadows previous x
IO.println x
```
The code block `C` for
```
IO.println x;
let x ← action₂; -- shadows previous x
IO.println x
```
is
```
Code.action (IO.println x) $
Code.vdecl _ x _ false action₂ $
Code.action (IO.println x) $
Code.return _ none []
```
Here is the incorrect way of extending it with the assignment `x := x + 1`.
```
Code.vdecl _ x _ true (x+1) $
Code.action (IO.println x) $
Code.vdecl _ x _ false action₂ $
Code.action (IO.println x) $
Code.return _ none [x]
```
The code above incorrectly returns the shadowed `x` as the updated value for `x`.
The process above using join-point produces the correct result:
```
Code.vdecl _ x _ true (x+1) $
Code.jdecl _ j [] (Code.return _ none [x]) $
Code.action (IO.println x) $
Code.vdecl _ x _ false action₂ $
Code.action (IO.println x) $
Code.jmp _ j []
```
The join point `j` returns the correct `x`.
-/

/-
Combining two code-blocks `C[us]` `D[vs]` into an if-then-else with condition `c`.
If `us == vs`, then it is easy. We just return:
```
Code.ite _ c C[us] D[us]
```
Otherwise, let `ws` be the union of `us` and `vs`. The for each `return`, `continue`, and `break` occurring in `C[us]` and `D[vs]`, we create
an auxiliary join point using a process similar to the one we used for extending code-blocks with reassignment operations.
For example, for a `break us` in `C[us]` we create a join point
```
Code.jdecl _ j [us] (Code.break [ws]) $ ...
```
and replace `break us` with `jmp _ j us`.
We call this operation `homogenise : Code → Code → Code × Code`. It takes two code blocks and returns two new code blocks that have the same
collection of updated variables.
Given `(C'[ws], D'[ws]) := homogenize C[us] D[vs]`, we return
```
ite c C'[ws] D'[ws]
```

The process of creating `match` terminal is similar.

-/

/-
We say a code-block `C[us]` is "terminal-like" if it is a sequence of join-point declarations followed by a `Code.ite` or `Code.match`.
That is, `C[us]` is obtained by the `mkIte` and `mkMatch` primitives.

For concatenating two joint points `C[us]` `D[vs]`, where `C[us]` is a terminal-like code block, we first consider the simpler case where `us == vs`,
then we use `homogenize` for implementing the general case.
If `us == vs`, we first create a joint point `j` for `D[us]`, and then replace each `return _ _ [us]` in `C[us]` with a `jmp j`, obtaining `C'[us]`.
The result is like
```
Code.jdecl _ j [] (D[us]) $
C'[us]
```
-/

end Do


structure ExtractMonadResult :=
(m           : Expr)
(α           : Expr)
(hasBindInst : Expr)

private def mkIdBindFor (type : Expr) : TermElabM ExtractMonadResult := do
u ← getLevel type;
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

private def getDoElems (stx : Syntax) : Array Syntax :=
let arg := stx.getArg 1;
let args := if arg.getKind == `Lean.Parser.Term.doSeqBracketed then
  (arg.getArg 1).getArgs
else
  arg.getArgs;
if args.back.isToken ";" then -- temporary hack
  args.pop
else
  args

private partial def hasLiftMethod : Syntax → Bool
| Syntax.node k args =>
  if k == `Lean.Parser.Term.do then false
  else if k == `Lean.Parser.Term.quot then false
  else if k == `Lean.Parser.Term.liftMethod then true
  else args.any hasLiftMethod
| _ => false

private partial def expandLiftMethodAux : Syntax → StateT (Array Syntax) MacroM Syntax
| stx@(Syntax.node k args) =>
  if k == `Lean.Parser.Term.do then pure stx
  else if k == `Lean.Parser.Term.quot then pure stx
  else if k == `Lean.Parser.Term.liftMethod then withFreshMacroScope $ do
    let term := args.get! 1;
    term ← expandLiftMethodAux term;
    auxDo ← `(do let a ← $term; $(Syntax.missing));
    let auxDoElems := (getDoElems auxDo).pop;
    modify $ fun s => s ++ auxDoElems;
    `(a)
  else do
    args ← args.mapM expandLiftMethodAux;
    pure $ Syntax.node k args
| stx => pure stx

private def expandLiftMethod (stx : Syntax) : MacroM (Option (Array Syntax)) :=
if hasLiftMethod stx then do
  (stx, doElems) ← (expandLiftMethodAux stx).run #[];
  let doElems := doElems.push stx;
  pure doElems
else
  pure none

/- Expand `doLet`, `doPat`, nonterminal `doExpr`s, and `liftMethod` -/
private partial def expandDoElems : Bool → Array Syntax → Nat → MacroM Syntax
| modified, doElems, i =>
  let mkRest : Unit → MacroM Syntax := fun _ => do {
    let restElems := doElems.extract (i+2) doElems.size;
    if restElems.size == 1 then
      pure $ (restElems.get! 0).getArg 0
    else
      `(do { $restElems* })
  };
  let addPrefix (rest : Syntax) : MacroM Syntax := do {
    if i == 0 then
      pure rest
    else
      let newElems := doElems.extract 0 i;
      let newElems := newElems.push $ Syntax.node `Lean.Parser.Term.doExpr #[rest];
      `(do { $newElems* })
  };
  if h : i < doElems.size then do
    let doElem := doElems.get ⟨i, h⟩;
    doElemsNew? ← expandLiftMethod doElem;
    match doElemsNew? with
    | some doElemsNew => do
      let post    := doElems.extract (i+1) doElems.size;
      let pre     := doElems.extract 0 i;
      let doElems := pre ++ doElemsNew ++ post;
      tmp ← `(do { $doElems* });
      expandDoElems true doElems i
    | none =>
      if doElem.getKind == `Lean.Parser.Term.doLet then do
        let letDecl := doElem.getArg 1;
        rest ← mkRest ();
        newBody ← `(let $letDecl:letDecl; $rest);
        addPrefix newBody
      -- cleanup the following code
      else if doElem.getKind == `Lean.Parser.Term.doLetArrow && (doElem.getArg 1).getKind == `Lean.Parser.Term.doPat then withFreshMacroScope $ do
        let doElem  := doElem.getArg 1;
        -- (termParser >> leftArrow) >> termParser >> optional (" | " >> termParser)
        let pat      := doElem.getArg 0;
        let discr    := doElem.getArg 2;
        let optElse  := doElem.getArg 3;
        rest ← mkRest ();
        newBody ←
          if optElse.isNone then do
            `(do let x ← $discr; (match x with | $pat => $rest))
          else
            let elseBody := optElse.getArg 1;
            `(do let x ← $discr; (match x with | $pat => $rest | _ => $elseBody));
        addPrefix newBody
      else if i < doElems.size - 1 && doElem.getKind == `Lean.Parser.Term.doExpr then do
        -- def doExpr := parser! termParser
        let term := doElem.getArg 0;
        auxDo ← `(do let x ← $term; $(Syntax.missing));
        let doElemNew := (getDoElems auxDo).get! 0;
        let doElems := doElems.set! i doElemNew;
        expandDoElems true doElems (i+2)
      else
        expandDoElems modified doElems (i+2)
  else if modified then
    `(do { $doElems* })
  else
    Macro.throwUnsupported

@[builtinMacro Lean.Parser.Term.do] def expandDo : Macro :=
fun stx =>
  let doElems := getDoElems stx;
  expandDoElems false doElems 0

structure ProcessedDoElem :=
(action : Expr)
(var    : Expr)

instance ProcessedDoElem.inhabited : Inhabited ProcessedDoElem := ⟨⟨arbitrary _, arbitrary _⟩⟩

private def extractTypeFormerAppArg (type : Expr) : TermElabM Expr := do
type ← withReducible $ whnf type;
match type with
| Expr.app _ a _ => pure a
| _              => throwError ("type former application expected" ++ indentExpr type)

/-
HasBind.bind : ∀ {m : Type u_1 → Type u_2} [self : HasBind m] {α β : Type u_1}, m α → (α → m β) → m β
-/
private def mkBind (m bindInstVal : Expr) (elems : Array ProcessedDoElem) (body : Expr) : TermElabM Expr :=
if elems.isEmpty then
  pure body
else do
  let x := elems.back.var; -- any variable would work since they must be in the same universe
  xType ← inferType x;
  u_1 ← getDecLevel xType;
  bodyType ← inferType body;
  u_2 ← getDecLevel bodyType;
  let bindAndInst := mkApp2 (Lean.mkConst `HasBind.bind [u_1, u_2]) m bindInstVal;
  elems.foldrM
    (fun elem body => do
      -- dbgTrace (">>> " ++ toString body);
      let var    := elem.var;
      let action := elem.action;
      α  ← inferType var;
      mβ ← inferType body;
      β  ← extractTypeFormerAppArg mβ;
      f  ← mkLambdaFVars #[var] body;
      -- dbgTrace (">>> f: " ++ toString f);
      let body := mkAppN bindAndInst #[α, β, action, f];
      pure body)
    body

private partial def processDoElemsAux (doElems : Array Syntax) (m bindInstVal : Expr) (expectedType : Expr) : Nat → Array ProcessedDoElem → TermElabM Expr
| i, elems =>
  let doElem := doElems.get! i;
  let k      := doElem.getKind;
  withRef doElem $
  if k == `Lean.Parser.Term.doLetArrow then do
    when (i == doElems.size - 1) $
      throwError "the last statement in a 'do' block must be an expression";
    let doElem := doElem.getArg 1;
    -- try (ident >> optType >> leftArrow) >> termParser
    let id        := doElem.getIdAt 0;
    let typeStx   := expandOptType doElem (doElem.getArg 1);
    let actionStx := doElem.getArg 3;
    type ← elabType typeStx;
    let actionExpectedType := mkApp m type;
    action ← elabTermEnsuringType actionStx actionExpectedType;
    withLocalDecl id BinderInfo.default type $ fun x =>
      processDoElemsAux (i+1) (elems.push { action := action, var := x })
  else if doElem.getKind == `Lean.Parser.Term.doExpr then do
    when (i != doElems.size - 1) $
      throwError ("unexpected 'do' expression element" ++ Format.line ++ doElem);
    let bodyStx := doElem.getArg 0;
    body ← elabTermEnsuringType bodyStx expectedType;
    mkBind m bindInstVal elems body
  else
    throwError ("unexpected 'do' expression element" ++ Format.line ++ doElem)

private def processDoElems (doElems : Array Syntax) (m bindInstVal : Expr) (expectedType : Expr) : TermElabM Expr :=
processDoElemsAux doElems m bindInstVal expectedType 0 #[]

@[builtinTermElab «do»] def elabDo : TermElab :=
fun stx expectedType? => do
  tryPostponeIfNoneOrMVar expectedType?;
  let doElems := getDoElems stx;
  trace `Elab.do $ fun _ => stx;
  let doElems := doElems.getSepElems;
  trace `Elab.do $ fun _ => "doElems: " ++ toString doElems;
  { m := m, hasBindInst := bindInstVal, .. } ← extractBind expectedType?;
  result ← processDoElems doElems m bindInstVal expectedType?.get!;
  -- dbgTrace ("result: " ++ toString result);
  pure result

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab.do;
pure ()

end Term
end Elab
end Lean
