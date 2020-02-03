/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Elab.Term
import Init.Lean.Elab.TermBinders
import Init.Lean.Elab.Quotation

namespace Lean
namespace Elab
namespace Term

structure ExtractMonadResult :=
(m           : Expr)
(α           : Expr)
(hasBindInst : Expr)

private def mkIdBindFor (ref : Syntax) (type : Expr) : TermElabM ExtractMonadResult := do
u ← getLevel ref type;
let id        := Lean.mkConst `Id [u];
let idBindVal := Lean.mkConst `Id.hasBind [u];
pure { m := id, hasBindInst := idBindVal, α := type }

private def extractBind (ref : Syntax) (expectedType? : Option Expr) : TermElabM ExtractMonadResult := do
match expectedType? with
| none => throwError ref "invalid do notation, expected type is not available"
| some expectedType => do
  type ← withReducible $ whnf ref expectedType;
  when type.getAppFn.isMVar $ throwError ref "invalid do notation, expected type is not available";
  match type with
  | Expr.app m α _ =>
    catch
      (do
        bindInstType ← mkAppM ref `HasBind #[m];
        bindInstVal  ← synthesizeInst ref bindInstType;
        pure { m := m, hasBindInst := bindInstVal, α := α })
      (fun ex => mkIdBindFor ref type)
  | _ => mkIdBindFor ref type

private def getDoElems (stx : Syntax) : Array Syntax :=
--parser! "do " >> (bracketedDoSeq <|> doSeq)
let arg := stx.getArg 1;
if arg.getKind == `Lean.Parser.Term.bracketedDoSeq then
  -- parser! "{" >> doSeq >> "}"
  (arg.getArg 1).getArgs
else
  arg.getArgs

private partial def hasLiftMethod : Syntax → Bool
| Syntax.node k args =>
  if k == `Lean.Parser.Term.do then false
  else if k == `Lean.Parser.Term.liftMethod then true
  else args.any hasLiftMethod
| _ => false

private partial def expandLiftMethodAux : Syntax → StateT (Array Syntax) MacroM Syntax
| stx@(Syntax.node k args) =>
  if k == `Lean.Parser.Term.do then pure stx
  else if k == `Lean.Parser.Term.liftMethod then withFreshMacroScope $ do
    let term := args.get! 1;
    term ← expandLiftMethodAux term;
    auxDo ← `(do a ← $term; $(Syntax.missing));
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
private partial def expandDoElemsAux : Bool → Array Syntax → Nat → MacroM (Option Syntax)
| modified, doElems, i =>
  let mkRest : Unit → MacroM Syntax := fun _ => do {
    let restElems := doElems.extract (i+2) doElems.size;
    if restElems.size == 1 then
      pure $ (restElems.get! 0).getArg 0
    else
      `(do { $restElems* })
  };
  let addPrefix (rest : Syntax) : MacroM (Option Syntax) := do {
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
      expandDoElemsAux true doElems i
    | none =>
      if doElem.getKind == `Lean.Parser.Term.doLet then do
        let letDecl := doElem.getArg 1;
        rest ← mkRest ();
        newBody ← `(let $letDecl:letDecl; $rest);
        addPrefix newBody
      else if doElem.getKind == `Lean.Parser.Term.doPat then withFreshMacroScope $ do
        -- (termParser >> leftArrow) >> termParser >> optional (" | " >> termParser)
        let pat      := doElem.getArg 0;
        let discr    := doElem.getArg 2;
        let optElse  := doElem.getArg 3;
        rest ← mkRest ();
        newBody ←
          if optElse.isNone then do
            `(do x ← $discr; match x with | $pat => $rest)
          else
            let elseBody := optElse.getArg 1;
            `(do x ← $discr; match x with | $pat => $rest | _ => $elseBody);
        addPrefix newBody
      else if i < doElems.size - 1 && doElem.getKind == `Lean.Parser.Term.doExpr then do
        -- def doExpr := parser! termParser
        let term := doElem.getArg 0;
        auxDo ← `(do x ← $term; $(Syntax.missing));
        let doElemNew := (getDoElems auxDo).get! 0;
        let doElems := doElems.set! i doElemNew;
        expandDoElemsAux true doElems (i+2)
      else
        expandDoElemsAux modified doElems (i+2)
  else if modified then
    `(do { $doElems* })
  else
    pure none

private partial def expandDoElems (doElems : Array Syntax) : MacroM (Option Syntax) :=
expandDoElemsAux false doElems 0

private def extractTypeFormer (ref : Syntax) (type : Expr) : TermElabM Expr := do
type ← withReducible $ whnf ref type;
match type with
| Expr.app m _ _ => pure m
| _              => throwError ref ("type former application expected" ++ indentExpr type)

private def extractTypeFormerAppArg (ref : Syntax) (type : Expr) : TermElabM Expr := do
type ← withReducible $ whnf ref type;
match type with
| Expr.app _ a _ => pure a
| _              => throwError ref ("type former application expected" ++ indentExpr type)

/-
Given an expected type of the form `n β` and a given type `m α`. We use the following approaches.

1- Try to unify `n` and `m`. If it succeeds, then we rely on the regular coercions, and
   the instances
   ```
   instance coeMethod {m : Type u → Type v} {α β : Type u} [∀ a, CoeT α a β] [Monad m] : Coe (m α) (m β)
   instance pureCoeDepProp {m : Type → Type v} [HasPure m] {p : Prop} [Decidable p] : CoeDep (m Prop) (pure p) (m Bool)
   ```

2- If there is monad lift from `m` to `n` and we can unify `α` and `β`, we use
  ```
  liftM : ∀ {m : Type u_1 → Type u_2} {n : Type u_1 → Type u_3} [self : HasMonadLiftT m n] {α : Type u_1}, m α → n α
  ```

3- If there is a monad lif from `m` to `n` and a coercion from `α` to `β`, we use
  ```
  liftCoeM {m : Type u → Type v} {n : Type u → Type w} {α β : Type u} [HasMonadLiftT m n] [∀ a, CoeT α a β] [Monad n] (x : m α) : n β
  ```

Note that approach 3 does not subsume 1 because it is only applicable if there is a coercion from `α` to `β` for all values in `α`.
This is not the case for example for `pure $ x > 0` when the expected type is `IO Bool`. The given type is `IO Prop`, and
we only have a coercion from decidable propositions.  Approach 1 works because it constructs the coercion `CoeT (m Prop) (pure $ x > 0) (m Bool)`
using the instance `pureCoeDepProp`.


We try to coerce first using `HasMonadLift` because it is more flexible than coercions.
Recall that type class resolution never assigns metavariables created by other modules.
Now, consider the following scenario
```lean
def g (x : Nat) : IO Nat := ...
deg h (x : Nat) : StateT Nat IO Nat := do
v ← g x;
IO.Println v;
...
```
Let's assume there is no other occurrence of `v` in `h`.
Thus, we have that the expected of `g x` is `StateT Nat IO ?α`,
and the given type is `IO Nat`. So, even if we add a coercion.
```
instance {α m n} [HasLiftT m n] {α} : Coe (m α) (n α) := ...
```
It is not applicable because TC would have to assign `?α := Nat`.
On the other hand, TC can easily solve `[HasLiftT IO (StateT Nat IO)]`
since this goal does not contain any metavariables. And then, we
convert `g x` into `liftM $ g x`.
-/
private def coeMethod (ref : Syntax) (expectedMonad : Expr) (expectedType : Expr) (val : Expr) (valType : Expr) : TermElabM Expr := do
m ← extractTypeFormer ref valType;
condM (isDefEq ref expectedMonad m)
  (ensureHasType ref expectedType val) -- approach 1 worked
  (do
    -- Construct lift from `m` to `n`
    α ← extractTypeFormerAppArg ref valType;
    hasMonadLiftType ← mkAppM ref `HasMonadLiftT #[m, expectedMonad];
    hasMonadLiftVal  ← synthesizeInst ref hasMonadLiftType;
    u_1 ← getDecLevel ref α;
    u_2 ← getDecLevel ref valType;
    u_3 ← getDecLevel ref expectedType;
    let newVal := mkAppN (Lean.mkConst `liftM [u_1, u_2, u_3]) #[m, expectedMonad, hasMonadLiftVal, α, val];
    newValType ← inferType ref newVal;
    condM (isDefEq ref expectedType newValType)
      (pure newVal) -- approach 2 worked
      (throwTypeMismatchError ref expectedType valType val)) -- TODO: approach 3

private def ensureDoElemType (ref : Syntax) (expectedMonad : Expr) (expectedType : Expr) (val : Expr) : TermElabM Expr := do
valType ← inferType ref val;
valType ← instantiateMVars ref valType;
condM (isDefEq ref valType expectedType) (pure val) $
  (coeMethod ref expectedMonad expectedType val valType)

structure ProcessedDoElem :=
(action : Expr)
(var    : Expr)

instance ProcessedDoElem.inhabited : Inhabited ProcessedDoElem := ⟨⟨arbitrary _, arbitrary _⟩⟩

/-
HasBind.bind : ∀ {m : Type u_1 → Type u_2} [self : HasBind m] {α β : Type u_1}, m α → (α → m β) → m β
-/
private def mkBind (ref : Syntax) (m bindInstVal : Expr) (elems : Array ProcessedDoElem) (body : Expr) : TermElabM Expr :=
if elems.isEmpty then
  pure body
else do
  let x := elems.back.var; -- any variable would work since they must be in the same universe
  xType ← inferType ref x;
  u_1 ← getDecLevel ref xType;
  bodyType ← inferType ref body;
  u_2 ← getDecLevel ref bodyType;
  let bindAndInst := mkApp2 (Lean.mkConst `HasBind.bind [u_1, u_2]) m bindInstVal;
  elems.foldrM
    (fun elem body => do
      -- dbgTrace (">>> " ++ toString body);
      let var    := elem.var;
      let action := elem.action;
      α  ← inferType ref var;
      mβ ← inferType ref body;
      β  ← extractTypeFormerAppArg ref mβ;
      f  ← mkLambda ref #[var] body;
      -- dbgTrace (">>> f: " ++ toString f);
      let body := mkAppN bindAndInst #[α, β, action, f];
      pure body)
    body

private partial def processDoElemsAux (doElems : Array Syntax) (m bindInstVal : Expr) (expectedType : Expr) : Nat → Array ProcessedDoElem → TermElabM Expr
| i, elems =>
  let doElem := doElems.get! i;
  let k      := doElem.getKind;
  let ref    := doElem;
  if k == `Lean.Parser.Term.doId then do
    when (i == doElems.size - 1) $
      throwError ref "the last statement in a 'do' block must be an expression";
    -- try (ident >> optType >> leftArrow) >> termParser
    let id        := doElem.getIdAt 0;
    let typeStx   := expandOptType ref (doElem.getArg 1);
    let actionStx := doElem.getArg 3;
    type ← elabType typeStx;
    let actionExpectedType := mkApp m type;
    action ← elabTerm actionStx actionExpectedType;
    action ← ensureDoElemType actionStx m actionExpectedType action;
    withLocalDecl ref id type $ fun x =>
      processDoElemsAux (i+1) (elems.push { action := action, var := x })
  else if doElem.getKind == `Lean.Parser.Term.doExpr then do
    when (i != doElems.size - 1) $
      throwError ref ("unexpected 'do' expression element" ++ Format.line ++ doElem);
    let bodyStx := doElem.getArg 0;
    body ← elabTerm bodyStx expectedType;
    body ← ensureDoElemType ref m expectedType body;
    mkBind ref m bindInstVal elems body
  else
    throwError ref ("unexpected 'do' expression element" ++ Format.line ++ doElem)

private def processDoElems (doElems : Array Syntax) (m bindInstVal : Expr) (expectedType : Expr) : TermElabM Expr :=
processDoElemsAux doElems m bindInstVal expectedType 0 #[]

@[builtinTermElab «do»] def elabDo : TermElab :=
fun stx expectedType? => do
  let ref := stx;
  tryPostponeIfNoneOrMVar expectedType?;
  let doElems := getDoElems stx;
  stxNew? ← liftMacroM $ expandDoElems doElems;
  match stxNew? with
  | some stxNew => withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?
  | none => do
    trace `Elab.do ref $ fun _ => stx;
    let doElems := doElems.getSepElems;
    { m := m, hasBindInst := bindInstVal, .. } ← extractBind ref expectedType?;
    result ← processDoElems doElems m bindInstVal expectedType?.get!;
    -- dbgTrace ("result: " ++ toString result);
    pure result

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab.do;
pure ()

end Term
end Elab
end Lean
