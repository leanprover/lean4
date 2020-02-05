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

/- Convert a path such as `[N.C.toB, N.B.toA]` into `#[ "." toB, "." toA]` -/
private def mkParentFieldNameFromPath (ref : Syntax) (path : List Name) : TermElabM (Array Syntax) :=
path.toArray.mapM $ fun toFunName =>
  match toFunName with
  | Name.str _ s _ => pure $ mkNullNode #[mkAtomFrom ref ".", mkIdentFrom ref (mkNameSimple s)]
  | _              => throwError ref "invalid field name to parent structure"

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
let args := (stx.getArg 2).getArgs;
args ← args.mapM $ fun arg =>
  if arg.getKind == `Lean.Parser.Term.structInstField then
    /- arg is of the form
       def structInstField  := parser! structInstLVal >> " := " >> termParser
       def structInstLVal   := (ident <|> structInstArrayRef) >> many (("." >> (ident <|> numLit)) <|> structInstArrayRef) -/
    let field := arg.getArg 0;
    if field.isIdent then
      let fieldName := field.getId;
      match findField? env structName fieldName with
      | none => throwError arg ("'" ++ fieldName ++ "' is not a field of structure '" ++ structName ++ "'")
      | some baseStructName =>
        if baseStructName == structName then pure arg
        else match getPathToBaseStructure? env baseStructName structName with
          | some (Name.str _ firstField _ :: rest) => do
            let newFieldStx  := mkIdentFrom arg (mkNameSimple firstField);
            let arg          := arg.setArg 0 newFieldStx;
            newFieldsStx ← mkParentFieldNameFromPath arg (rest ++ [fieldName]);
            let newManyArgs  := newFieldsStx ++ (arg.getArg 1).getArgs;
            let arg          := arg.setArg 1 (mkNullNode newManyArgs);
            pure arg
          | _ => throwError arg ("failed to access field '" ++ fieldName ++ "' in parent structure")
    else
      pure arg
  else
    pure arg;
pure $ stx.setArg 2 (mkNullNode args)

private def elabStructInstAux (stx : Syntax) (expectedType? : Option Expr) (sourceView : SourceView) : TermElabM Expr := do
structName ← getStructName stx expectedType? sourceView;
env ← getEnv;
unless (isStructureLike env structName) $
  throwError stx ("invalid {...} notation, '" ++ structName ++ "' is not a structure");
stx ← expandParentFields stx structName;
throwError stx ("WIP " ++ toString structName ++ toString stx)

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
