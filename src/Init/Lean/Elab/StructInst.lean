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

/- parser! symbol "{" appPrec >> optional (try (ident >> " . ")) >> sepBy (structInstField <|> structInstSource) ", " true >> "}" -/

namespace ExpandNonAtomicExplicitSource

structure State :=
(found : Bool := false)
(source? : Option Syntax := none)

/- Auxiliary function for  `expandNonAtomicExplicitSource` -/
def main (stx : Syntax) : StateT State TermElabM (Option Syntax) := do
let args := (stx.getArg 2).getArgs;
args ← args.mapM $ fun arg =>
  if arg.getKind == `Lean.Parser.Term.structInstSource then do
    -- parser! ".." >> optional termParser
    s ← get;
    if s.found then
      liftM $ throwError arg "source has already been specified"
    else
      let optSource := arg.getArg 1;
      if optSource.isNone then do
        modify $ fun s => { found := true, .. s };
        pure arg
      else do
        let source := optSource.getArg 0;
        fvar? ← liftM $ isLocalTermId? source;
        match fvar? with
        | some _ => do
          -- it is already a local variable
          modify $ fun s => { found := true, .. s };
          pure arg
        | none => do
          src ← `(src);
          modify $ fun s => { found := true, source? := source, .. s };
          let optSource := optSource.setArg 0 src;
          let arg := arg.setArg 1 optSource;
          pure arg
  else
    pure arg;
s ← get;
match s.source? with
| none        => pure none
| some source => do
  let newStx := stx.setArg 2 (mkNullNode args);
  `(let src := $source; $newStx)

end ExpandNonAtomicExplicitSource

/-
If `stx` is of the form `{ ... .. s }` and `s` is not a local variable, expand into `let src := s; { ... .. src}`.
-/
def expandNonAtomicExplicitSource (stx : Syntax) : TermElabM (Option Syntax) :=
withFreshMacroScope $ (ExpandNonAtomicExplicitSource.main stx).run' {}

inductive SourceView
| none     -- structure instance source has not been provieded
| implicit -- `..`
| explicit (stx : Syntax) -- `.. term`

def SourceView.isNone : SourceView → Bool
| SourceView.none => true
| _               => false

private def getStructSource (stx : Syntax) : TermElabM SourceView :=
let args := (stx.getArg 2).getArgs;
args.foldSepByM
  (fun arg r =>
    if arg.getKind == `Lean.Parser.Term.structInstSource then
      -- parser! ".." >> optional termParser
      if !r.isNone then throwError arg "source has already been specified"
      else
        let arg := arg.getArg 1;
        if arg.isNone then pure SourceView.implicit
        else pure $ SourceView.explicit (arg.getArg 0)
    else
      pure r)
  SourceView.none

/-
  We say a `{ ... }` notation is a `modifyOp` if it contains only one
  ```
  def structInstArrayRef := parser! "[" >> termParser >>"]"
  ``` -/
private def isModifyOp? (stx : Syntax) : TermElabM (Option Syntax) := do
let args := (stx.getArg 2).getArgs;
s? ← args.foldSepByM
  (fun arg s? =>
    let k := arg.getKind;
    if k == `Lean.Parser.Term.structInstSource then pure s?
    else if k == `Lean.Parser.Term.structInstArrayRef then
      match s? with
      | none   => pure (some arg)
      | some s =>
        if s.getKind == `Lean.Parser.Term.structInstArrayRef then
          throwError arg "invalid {...} notation, at most one `[..]` at a given level"
        else
          throwError arg "invalid {...} notation, can't mix field and `[..]` at a given level"
    else
      match s? with
      | none   => pure (some arg)
      | some s =>
        if s.getKind == `Lean.Parser.Term.structInstArrayRef then
          throwError arg "invalid {...} notation, can't mix field and `[..]` at a given level"
        else
          pure s?)
  none;
match s? with
| none   => pure none
| some s => if s.getKind == `Lean.Parser.Term.structInstArrayRef then pure s? else pure none

private def elabModifyOp (stx modifyOp source : Syntax) (expectedType? : Option Expr) : TermElabM Expr :=
throwError stx ("WIP " ++ stx)

/- Get structure name and elaborate explicit source (if avialable) -/
private def getStructName (stx : Syntax) (expectedType? : Option Expr) (sourceView : SourceView) : TermElabM Name :=
let arg := stx.getArg 1;
if !arg.isNone then do
  pure $ arg.getIdAt 0
else do
  let ref := stx;
  tryPostponeIfNoneOrMVar expectedType?;
  let useSource : Unit → TermElabM Name := fun _ =>
    match sourceView with
    | SourceView.explicit sourceStx => do
      fvar? ← isLocalTermId? sourceStx;
      match fvar? with
      | none => unreachable!
      | some fvar => do
        fvarType ← inferType stx fvar;
        fvarType ← whnf stx fvarType;
        tryPostponeIfMVar fvarType;
        match fvarType.getAppFn with
        | Expr.const constName _ _ => pure constName
        | _ => throwError stx ("invalid {...} notation, source type is not of the form (C ...)" ++ indentExpr fvarType)
    | _ => throwError ref ("invalid {...} notation, expected type is not of the form (C ...)" ++ indentExpr expectedType?.get!);
  match expectedType? with
  | none => useSource ()
  | some expectedType => do
    expectedType ← whnf ref expectedType;
    match expectedType.getAppFn with
    | Expr.const constName _ _ => pure constName
    | _                        => useSource ()

/-
Recall that `structInstField` elements have the form
```
   def structInstField  := parser! structInstLVal >> " := " >> termParser
   def structInstLVal   := (ident <|> numLit <|> structInstArrayRef) >> many (("." >> (ident <|> numLit)) <|> structInstArrayRef)
-/

/- Given a structure instance element `structInstElem`, prepend the new fields. -/
private def prependFields (structInstElem : Syntax) (newFields : List Name) : Syntax :=
match newFields with
| []            => structInstElem
| first :: rest =>
  let currFirst      := structInstElem.getArg 0;
  let currFirst      := if currFirst.isIdent then mkNullNode #[mkAtomFrom currFirst ".", currFirst] else currFirst;
  let restStx        := rest.toArray.map $ fun fieldName => mkNullNode #[mkAtomFrom structInstElem ".", mkIdentFrom structInstElem fieldName];
  let newManyArgs    := restStx.push currFirst ++ (structInstElem.getArg 1).getArgs;
  let structInstElem := structInstElem.setArg 1 (mkNullNode newManyArgs);
  structInstElem.setArg 0 (mkIdentFrom structInstElem first)

@[inline] private def modifyStructInstFieldsM {m : Type → Type} [Monad m] (stx : Syntax) (f : Syntax → m Syntax) : m Syntax := do
let args := (stx.getArg 2).getArgs;
args ← args.mapM $ fun arg =>
  if arg.getKind == `Lean.Parser.Term.structInstField then
    f arg
  else
    pure arg;
pure $ stx.setArg 2 (mkNullNode args)

@[inline] private def modifyStructInstFields (stx : Syntax) (f : Syntax → Syntax) : Syntax :=
Id.run $ modifyStructInstFieldsM stx f

/- Given a structure instance `stx`, expand the first field of each element if it is a composite name.
   Example:
   ```
   (Term.structInstField `x.y (null) ":=" (Term.num (numLit "1")))
   ```
   is expanded into
   ```
   (Term.structInstField `x (null (null "." `y)) ":=" (Term.num (numLit "1")))
   ``` -/
private def expandCompositeFields (stx : Syntax) : Syntax :=
modifyStructInstFields stx $ fun arg =>
  let field := arg.getArg 0;
  if field.isIdent then
    match field.getId with
    | Name.str Name.anonymous _ _ => arg -- atomic field
    | Name.str pre s _ =>
      -- update first with `s`
      let arg := arg.setArg 0 (mkIdentFrom field (mkNameSimple s));
      prependFields arg pre.components
    | _ => unreachable!
  else
    arg

/- Example `{ Prod . 1 := 10, 2 := true }` => `{ Prod . fst := 10, snd := true }` -/
private def expandNumLitFields (stx : Syntax) (structName : Name) : TermElabM Syntax := do
env ← getEnv;
let fieldNames := getStructureFields env structName;
modifyStructInstFieldsM stx $ fun arg =>
  let field := arg.getArg 0;
  match field.isNatLit? with
  | none     => pure arg
  | some idx =>
    if idx == 0 then throwError arg "invalid field index, index must be greater than 0"
    else if idx > fieldNames.size then throwError arg ("invalid field index, structure has only #" ++ toString fieldNames.size ++ " fields")
    else
      let newField := mkIdentFrom field (fieldNames.get! idx);
      pure $ arg.setArg 0 newField

/- For example, consider the following structures:
   ```
   structure A := (x : Nat)
   structure B extends A := (y : Nat)
   structure C extends B := (z : Bool)
   ```
   This method expands parent structure fields using the path to the parent structure.
   For example,
   ```
   { C . x := 0, y := 0, z := true }
   ```
   is expanded into
   ```
   { C . toB.toA.x := 0, toB.y := 0, z := true }
   ``` -/
private def expandParentFields (stx : Syntax) (structName : Name) : TermElabM Syntax := do
env ← getEnv;
modifyStructInstFieldsM stx $ fun arg =>
  let field := arg.getArg 0;
  if field.isIdent then
    let fieldName := field.getId;
    match findField? env structName fieldName with
    | none => throwError arg ("'" ++ fieldName ++ "' is not a field of structure '" ++ structName ++ "'")
    | some baseStructName =>
      if baseStructName == structName then pure arg
      else match getPathToBaseStructure? env baseStructName structName with
        | some path => do
          let path := path.map $ fun funName => match funName with
            | Name.str _ s _ => mkNameSimple s
            | _              => unreachable!;
          pure $ prependFields arg path
        | _ => throwError arg ("failed to access field '" ++ fieldName ++ "' in parent structure")
  else
    pure arg

/- We say a `structInstField` is simple if the suffix is empty.
   That is, the `many` component `many (("." >> (ident <|> numLit)) <|> structInstArrayRef)` is empty. -/
private def isSimpleStructInstField (stx : Syntax) : Bool :=
(stx.getArg 1).getArgs.isEmpty

private def getStructInstFields (stx : Syntax) : Array Syntax :=
(stx.getArg 2).getArgs.filter $ fun elem => elem.getKind == `Lean.Parser.Term.structInstField

private def getFieldName (structInstField : Syntax) : Name :=
(structInstField.getArg 0).getId

private abbrev FieldMap := HashMap Name (List Syntax)

private def groupFields (instFields : Array Syntax) : TermElabM FieldMap :=
instFields.foldlM
  (fun fieldMap instField =>
    let fieldName := getFieldName instField;
    match fieldMap.find? fieldName with
    | some (prevInstField::restInstFields) =>
      if isSimpleStructInstField prevInstField || isSimpleStructInstField instField then
        throwError instField ("field '" ++ fieldName ++ "' has already beed specified")
      else
        pure $ fieldMap.insert fieldName (instField::prevInstField::restInstFields)
    | _ => pure $ fieldMap.insert fieldName [instField])
  {}

private def isSimpleStructInstFieldSingleton? : List Syntax → Option Syntax
| [instField] => if isSimpleStructInstField instField then some instField else none
| _           => none

-- def structInstSource := parser! ".." >> optional termParser
private def mkStructInstSource (ref : Syntax) (optTermParser : Syntax) : Syntax :=
Syntax.node `Lean.Parser.Term.structInstSource #[mkAtomFrom ref "..", optTermParser]

private def mkProjStx (s : Syntax) (fieldName : Name) : Syntax :=
Syntax.node `Lean.Parser.Term.proj #[s, mkAtomFrom s ".", mkIdentFrom s fieldName]

structure FieldView :=
(ref : Syntax)
(fieldName : Name)
(val: Syntax)

private def getFields (stx : Syntax) (sourceView : SourceView) : TermElabM (List FieldView) := do
let instFields := getStructInstFields stx;
fieldMap ← groupFields instFields;
pure $ fieldMap.toList.map $ fun ⟨fieldName, instFields⟩ =>
  match isSimpleStructInstFieldSingleton? instFields with
  | some instField => { ref := instField, fieldName := fieldName, val := instField.getArg 3 }
  | none =>
    let newArgs := instFields.toArray.map $ fun instField =>
      let suffixElems    := (instField.getArg 1).getArgs;
      let newField       := suffixElems.get! 0;
      let newField       := if newField.getKind == `Lean.Parser.Term.structInstArrayRef then newField else newField.getArg 1;
      let newSuffixElems := suffixElems.eraseIdx 0;
      let instField      := instField.setArg 0 newField;
      let instField      := instField.setArg 1 (mkNullNode newSuffixElems);
      instField;
    let newArgs := match sourceView with
      | SourceView.none         => newArgs
      | SourceView.implicit     => newArgs.push $ mkStructInstSource stx mkNullNode
      | SourceView.explicit src => newArgs.push $ mkStructInstSource stx (mkNullNode #[mkProjStx src fieldName]);
    let newStruct := stx.setArg 1 mkNullNode; -- erase explicit struct name
    let newStruct := stx.setArg 2 (mkSepStx newArgs (mkAtomFrom stx ","));
    { ref := instFields.head!, fieldName := fieldName, val := newStruct }

private def elabStructInstAux (stx : Syntax) (expectedType? : Option Expr) (sourceView : SourceView) : TermElabM Expr := do
structName ← getStructName stx expectedType? sourceView;
env ← getEnv;
unless (isStructureLike env structName) $
  throwError stx ("invalid {...} notation, '" ++ structName ++ "' is not a structure");
let stx := expandCompositeFields stx;
stx ← expandNumLitFields stx structName;
stx ← expandParentFields stx structName;
fieldViews ← getFields stx sourceView;
fieldViews.forM $ fun v => dbgTrace (toString v.fieldName ++ " := " ++ toString v.val);
throwError stx ("WIP")

@[builtinTermElab structInst] def elabStructInst : TermElab :=
fun stx expectedType? => do
  stxNew? ← expandNonAtomicExplicitSource stx;
  match stxNew? with
  | some stxNew => withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?
  | none => do
    sourceView ← getStructSource stx;
    modifyOp?  ← isModifyOp? stx;
    match modifyOp?, sourceView with
    | some modifyOp, SourceView.explicit source => elabModifyOp stx modifyOp source expectedType?
    | some _,        _                          => throwError stx ("invalid {...} notation, explicit source is required when using '[<index>] := <value>'")
    | _,             _                          => elabStructInstAux stx expectedType? sourceView

end Term
end Elab
end Lean
