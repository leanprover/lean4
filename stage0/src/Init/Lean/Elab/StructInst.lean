/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Util.FindExpr
import Init.Lean.Elab.App
import Init.Lean.Elab.Binders
import Init.Lean.Elab.Quotation

namespace Lean
namespace Elab
namespace Term
namespace StructInst

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
private def expandNonAtomicExplicitSource (stx : Syntax) : TermElabM (Option Syntax) :=
withFreshMacroScope $ (ExpandNonAtomicExplicitSource.main stx).run' {}

inductive Source
| none     -- structure instance source has not been provieded
| implicit (stx : Syntax) -- `..`
| explicit (stx : Syntax) (src : Expr) -- `.. term`

instance Source.inhabited : Inhabited Source := ⟨Source.none⟩

def Source.isNone : Source → Bool
| Source.none => true
| _           => false

instance Source.hasFormat : HasFormat Source :=
⟨fun src => match src with
 | Source.none           => ""
 | Source.implicit _     => " .."
 | Source.explicit _ src => " .. " ++ format src⟩

def Source.addSyntax : Source → Array Syntax → Array Syntax
| Source.none,           acc => acc
| Source.implicit stx,   acc => acc.push stx
| Source.explicit stx _, acc => acc.push stx

private def getStructSource (stx : Syntax) : TermElabM Source :=
let args := (stx.getArg 2).getArgs;
args.foldSepByM
  (fun arg r =>
    if arg.getKind == `Lean.Parser.Term.structInstSource then
      -- parser! ".." >> optional termParser
      if !r.isNone then throwError arg "source has already been specified"
      else
        let optTerm := arg.getArg 1;
        if optTerm.isNone then pure $ Source.implicit arg
        else do
          fvar? ← isLocalTermId? (optTerm.getArg 0);
          match fvar? with
          | none      => unreachable! -- expandNonAtomicExplicitSource must have been used when we get here
          | some fvar => pure $ Source.explicit arg fvar
    else
      pure r)
  Source.none

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

private def elabModifyOp (stx modifyOp : Syntax) (source : Expr) (expectedType? : Option Expr) : TermElabM Expr :=
throwError stx ("WIP " ++ stx)

/- Get structure name and elaborate explicit source (if avialable) -/
private def getStructName (stx : Syntax) (expectedType? : Option Expr) (sourceView : Source) : TermElabM Name :=
let arg := stx.getArg 1;
if !arg.isNone then do
  r : List (Name × List String) ← resolveGlobalName (arg.getIdAt 0);
  env ← getEnv;
  let r := r.filter $ fun p => p.2.isEmpty && isStructureLike env p.1;
  let candidates := r.map $ fun p => p.1;
  match candidates with
  | [c] => pure c
  | []  => throwError arg "invalid {...} notation, structure expected"
  | _   => throwError arg ("invalid {...} notation, ambiguous " ++ toString candidates)
else do
  let ref := stx;
  tryPostponeIfNoneOrMVar expectedType?;
  let useSource : Unit → TermElabM Name := fun _ =>
    match sourceView with
    | Source.explicit _ src => do
      srcType ← inferType stx src;
      srcType ← whnf stx srcType;
      tryPostponeIfMVar srcType;
      match srcType.getAppFn with
      | Expr.const constName _ _ => pure constName
      | _ => throwError stx ("invalid {...} notation, source type is not of the form (C ...)" ++ indentExpr srcType)
    | _ => throwError ref ("invalid {...} notation, expected type is not of the form (C ...)" ++ indentExpr expectedType?.get!);
  match expectedType? with
  | none => useSource ()
  | some expectedType => do
    expectedType ← whnf ref expectedType;
    match expectedType.getAppFn with
    | Expr.const constName _ _ => pure constName
    | _                        => useSource ()

inductive FieldLHS
| fieldName  (ref : Syntax) (name : Name)
| fieldIndex (ref : Syntax) (idx : Nat)
| modifyOp   (ref : Syntax) (index : Syntax)

instance FieldLHS.inhabited : Inhabited FieldLHS := ⟨FieldLHS.fieldName (arbitrary _) (arbitrary _)⟩
instance FieldLHS.hasFormat : HasFormat FieldLHS :=
⟨fun lhs => match lhs with
  | FieldLHS.fieldName _ n  => fmt n
  | FieldLHS.fieldIndex _ i => fmt i
  | FieldLHS.modifyOp _ i   => "[" ++ i.prettyPrint ++ "]"⟩

inductive FieldVal (σ : Type)
| term {} (stx : Syntax) : FieldVal
| nested (s : σ)         : FieldVal
| default {}             : FieldVal -- mark that field must be synthesized using default value

structure Field (σ : Type) :=
mk {} :: (ref : Syntax) (lhs : List FieldLHS) (val : FieldVal σ) (expr? : Option Expr := none)

instance Field.inhabited {σ} : Inhabited (Field σ) := ⟨⟨arbitrary _, [], FieldVal.term (arbitrary _), arbitrary _⟩⟩

def Field.isSimple {σ} : Field σ → Bool
| { lhs := [_], .. } => true
| _                  => false

inductive Struct
| mk (ref : Syntax) (structName : Name) (fields : List (Field Struct)) (source : Source)

instance Struct.inhabited : Inhabited Struct := ⟨⟨arbitrary _, arbitrary _, [], arbitrary _⟩⟩

abbrev Fields := List (Field Struct)

def Struct.ref : Struct → Syntax
| ⟨ref, _, _, _⟩ => ref

def Struct.structName : Struct → Name
| ⟨_, structName, _, _⟩ => structName

def Struct.fields : Struct → Fields
| ⟨_, _, fields, _⟩ => fields

def Struct.source : Struct → Source
| ⟨_, _, _, s⟩ => s

def formatField (formatStruct : Struct → Format) (field : Field Struct) : Format :=
Format.joinSep field.lhs " . " ++ " := " ++
  match field.val with
  | FieldVal.term v   => v.prettyPrint
  | FieldVal.nested s => formatStruct s
  | FieldVal.default  => "<default>"

partial def formatStruct : Struct → Format
| ⟨_, structName, fields, source⟩ =>
  "{" ++ fmt structName ++ " . " ++ Format.joinSep (fields.map (formatField formatStruct)) ", " ++ fmt source ++ "}"

instance Struct.hasFormat : HasFormat Struct     := ⟨formatStruct⟩
instance Struct.hasToString : HasToString Struct := ⟨toString ∘ format⟩

instance Field.hasFormat   : HasFormat (Field Struct) := ⟨formatField formatStruct⟩
instance Field.hasToString : HasToString (Field Struct) := ⟨toString ∘ format⟩

/-
Recall that `structInstField` elements have the form
```
   def structInstField  := parser! structInstLVal >> " := " >> termParser
   def structInstLVal   := (ident <|> numLit <|> structInstArrayRef) >> many (("." >> (ident <|> numLit)) <|> structInstArrayRef)
   def structInstArrayRef := parser! "[" >> termParser >>"]"
-/

-- Remark: this code relies on the fact that `expandStruct` only transforms `fieldLHS.fieldName`
def FieldLHS.toSyntax (first : Bool) : FieldLHS → Syntax
| FieldLHS.modifyOp   stx _    => stx
| FieldLHS.fieldName  stx name => if first then mkIdentFrom stx name else mkNullNode #[mkAtomFrom stx ".", mkIdentFrom stx name]
| FieldLHS.fieldIndex stx _    => if first then stx else mkNullNode #[mkAtomFrom stx ".", stx]

def FieldVal.toSyntax : FieldVal Struct → Syntax
| FieldVal.term stx => stx
| _                 => unreachable!

def Field.toSyntax : Field Struct → Syntax
| field =>
  let stx := field.ref;
  let stx := stx.setArg 3 field.val.toSyntax;
  match field.lhs with
  | first::rest =>
    let stx := stx.setArg 0 $ first.toSyntax true;
    let stx := stx.setArg 1 $ mkNullNode $ rest.toArray.map (FieldLHS.toSyntax false);
    stx
  | _ => unreachable!

private def toFieldLHS (stx : Syntax) : FieldLHS :=
if stx.getKind == `Lean.Parser.Term.structInstArrayRef then FieldLHS.modifyOp stx (stx.getArg 1)
else
  -- Note that the representation of the first field is different.
  let stx := if stx.getKind == nullKind then stx.getArg 1 else stx;
  if stx.isIdent then FieldLHS.fieldName stx stx.getId
  else match stx.isNatLit? with
    | some idx => FieldLHS.fieldIndex stx idx
    | none     => unreachable!

private def mkStructView (stx : Syntax) (structName : Name) (source : Source) : Struct :=
let args      := (stx.getArg 2).getArgs;
let fieldsStx := args.filter $ fun arg => arg.getKind == `Lean.Parser.Term.structInstField;
let fields := fieldsStx.toList.map $ fun fieldStx =>
  let val   := fieldStx.getArg 3;
  let first := toFieldLHS (fieldStx.getArg 0);
  let rest  := (fieldStx.getArg 1).getArgs.toList.map $ toFieldLHS;
  ({ref := fieldStx, lhs := first :: rest, val := FieldVal.term val } : Field Struct);
⟨stx, structName, fields, source⟩

def Struct.modifyFieldsM {m : Type → Type} [Monad m] (s : Struct) (f : Fields → m Fields) : m Struct :=
match s with
| ⟨ref, structName, fields, source⟩ => do fields ← f fields; pure ⟨ref, structName, fields, source⟩

@[inline] def Struct.modifyFields (s : Struct) (f : Fields → Fields) : Struct :=
Id.run $ s.modifyFieldsM f

def Struct.setFields (s : Struct) (fields : Fields) : Struct :=
s.modifyFields $ fun _ => fields

private def expandCompositeFields (s : Struct) : Struct :=
s.modifyFields $ fun fields => fields.map $ fun field => match field with
  | { lhs := FieldLHS.fieldName ref (Name.str Name.anonymous _ _) :: rest, .. } => field
  | { lhs := FieldLHS.fieldName ref n@(Name.str _ _ _) :: rest, .. } =>
    let newEntries := n.components.map $ FieldLHS.fieldName ref;
    { lhs := newEntries ++ rest, .. field }
  | _ => field

private def expandNumLitFields (s : Struct) : TermElabM Struct :=
s.modifyFieldsM $ fun fields => do
  env ← getEnv;
  let fieldNames := getStructureFields env s.structName;
  fields.mapM $ fun field => match field with
    | { lhs := FieldLHS.fieldIndex ref idx :: rest, .. } =>
      if idx == 0 then throwError ref "invalid field index, index must be greater than 0"
      else if idx > fieldNames.size then throwError ref ("invalid field index, structure has only #" ++ toString fieldNames.size ++ " fields")
      else pure { lhs := FieldLHS.fieldName ref (fieldNames.get! $ idx - 1) :: rest, .. field }
    | _ => pure field

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
private def expandParentFields (s : Struct) : TermElabM Struct := do
env ← getEnv;
s.modifyFieldsM $ fun fields => fields.mapM $ fun field => match field with
  | { lhs := FieldLHS.fieldName ref fieldName :: rest, .. } =>
    match findField? env s.structName fieldName with
    | none => throwError ref ("'" ++ fieldName ++ "' is not a field of structure '" ++ s.structName ++ "'")
    | some baseStructName =>
      if baseStructName == s.structName then pure field
      else match getPathToBaseStructure? env baseStructName s.structName with
        | some path => do
          let path := path.map $ fun funName => match funName with
            | Name.str _ s _ => FieldLHS.fieldName ref (mkNameSimple s)
            | _              => unreachable!;
          pure { lhs := path ++ field.lhs, .. field }
        | _ => throwError ref ("failed to access field '" ++ fieldName ++ "' in parent structure")
  | _ => pure field

private abbrev FieldMap := HashMap Name Fields

private def mkFieldMap (fields : Fields) : TermElabM FieldMap :=
fields.foldlM
  (fun fieldMap field =>
    match field.lhs with
    | FieldLHS.fieldName _ fieldName :: rest =>
      match fieldMap.find? fieldName with
      | some (prevField::restFields) =>
        if field.isSimple || prevField.isSimple then
          throwError field.ref ("field '" ++ fieldName ++ "' has already beed specified")
        else
          pure $ fieldMap.insert fieldName (field::prevField::restFields)
      | _ => pure $ fieldMap.insert fieldName [field]
    | _ => unreachable!)
  {}

private def isSimpleField? : Fields → Option (Field Struct)
| [field] => if field.isSimple then some field else none
| _       => none

private def getFieldIdx (ref : Syntax) (structName : Name) (fieldNames : Array Name) (fieldName : Name) : TermElabM Nat := do
match fieldNames.findIdx? $ fun n => n == fieldName with
| some idx => pure idx
| none     => throwError ref ("field '" ++ fieldName ++ "' is not a valid field of '" ++ structName ++ "'")

private def mkProjStx (s : Syntax) (fieldName : Name) : Syntax :=
Syntax.node `Lean.Parser.Term.proj #[s, mkAtomFrom s ".", mkIdentFrom s fieldName]

private def mkSubstructSource (ref : Syntax) (structName : Name) (fieldNames : Array Name) (fieldName : Name) (src : Source) : TermElabM Source :=
match src with
| Source.explicit stx src => do
  idx ← getFieldIdx ref structName fieldNames fieldName;
  let stx := stx.modifyArg 1 $ fun stx => stx.modifyArg 0 $ fun stx => mkProjStx stx fieldName;
  pure $ Source.explicit stx (mkProj structName idx src)
| s => pure s

@[specialize] private def groupFields (expandStruct : Struct → TermElabM Struct) (s : Struct) : TermElabM Struct := do
env ← getEnv;
let fieldNames := getStructureFields env s.structName;
s.modifyFieldsM $ fun fields => do
  fieldMap ← mkFieldMap fields;
  fieldMap.toList.mapM $ fun ⟨fieldName, fields⟩ =>
    match isSimpleField? fields with
    | some field => pure field
    | none => do
      let substructFields := fields.map $ fun field => { lhs := field.lhs.tail!, .. field };
      substructSource ← mkSubstructSource s.ref s.structName fieldNames fieldName s.source;
      let field := fields.head!;
      match Lean.isSubobjectField? env s.structName fieldName with
      | some substructName => do
        let substruct := Struct.mk s.ref substructName substructFields substructSource;
        substruct ← expandStruct substruct;
        pure { lhs := [field.lhs.head!], val := FieldVal.nested substruct, .. field }
      | none => do
        -- It is not a substructure field. Thus, we wrap fields using `Syntax`, and use `elabTerm` to process them.
        let valStx := s.ref; -- construct substructure syntax using s.ref as template
        let valStx := valStx.setArg 1 mkNullNode; -- erase optional struct name
        let args   := substructFields.toArray.map $ Field.toSyntax;
        let args   := substructSource.addSyntax args;
        let valStx := valStx.setArg 2 (mkSepStx args (mkAtomFrom s.ref ","));
        pure { lhs := [field.lhs.head!], val := FieldVal.term valStx, .. field }

def findField? (fields : Fields) (fieldName : Name) : Option (Field Struct) :=
fields.find? $ fun field =>
  match field.lhs with
  | [FieldLHS.fieldName _ n] => n == fieldName
  | _                        => false

@[specialize] private def addMissingFields (expandStruct : Struct → TermElabM Struct) (s : Struct) : TermElabM Struct := do
env ← getEnv;
let fieldNames := getStructureFields env s.structName;
let ref := s.ref;
fields ← fieldNames.foldlM
  (fun fields fieldName => do
    match findField? s.fields fieldName with
    | some field => pure $ field::fields
    | none       =>
      let addField (val : FieldVal Struct) : TermElabM Fields := do {
        pure $ { ref := s.ref, lhs := [FieldLHS.fieldName s.ref fieldName], val := val } :: fields
      };
      match Lean.isSubobjectField? env s.structName fieldName with
      | some substructName => do
        substructSource ← mkSubstructSource s.ref s.structName fieldNames fieldName s.source;
        let substruct := Struct.mk s.ref substructName [] substructSource;
        substruct ← expandStruct substruct;
        addField (FieldVal.nested substruct)
      | none =>
        match s.source with
        | Source.none           => addField FieldVal.default
        | Source.implicit _     => addField (FieldVal.term (mkHole s.ref))
        | Source.explicit stx _ =>
          -- stx is of the form `".." >> optional termParser`
          let src := (stx.getArg 1).getArg 0;
          let val := mkProjStx src fieldName;
          addField (FieldVal.term val))
  [];
pure $ s.setFields fields.reverse

private partial def expandStruct : Struct → TermElabM Struct
| s => do
  let s := expandCompositeFields s;
  s ← expandNumLitFields s;
  s ← expandParentFields s;
  s ← groupFields expandStruct s;
  addMissingFields expandStruct s

structure CtorHeaderResult :=
(ctorFn     : Expr)
(ctorFnType : Expr)
(instMVars  : Array MVarId := #[])

private def mkCtorHeaderAux (ref : Syntax) : Nat → Expr → Expr → Array MVarId → TermElabM CtorHeaderResult
| 0,   type, ctorFn, instMVars => pure { ctorFn := ctorFn, ctorFnType := type, instMVars := instMVars }
| n+1, type, ctorFn, instMVars => do
  type ← whnfForall ref type;
  match type with
  | Expr.forallE _ d b c =>
    match c.binderInfo with
    | BinderInfo.instImplicit => do
      a ← mkFreshExprMVar ref d MetavarKind.synthetic;
      mkCtorHeaderAux n (b.instantiate1 a) (mkApp ctorFn a) (instMVars.push a.mvarId!)
    | _ => do
      a ← mkFreshExprMVar ref d;
      mkCtorHeaderAux n (b.instantiate1 a) (mkApp ctorFn a) instMVars
  | _ => throwError ref "unexpected constructor type"

private partial def getForallBody : Nat → Expr → Option Expr
| i+1, Expr.forallE _ _ b _ => getForallBody i b
| i+1, _                    => none
| 0,   type                 => type

private def propagateExpectedType (ref : Syntax) (type : Expr) (numFields : Nat) (expectedType? : Option Expr) : TermElabM Unit :=
match expectedType? with
| none              => pure ()
| some expectedType =>
  match getForallBody numFields type with
    | none           => pure ()
    | some typeBody =>
      unless typeBody.hasLooseBVars $ do
        isDefEq ref expectedType typeBody;
        pure ()

private def mkCtorHeader (ref : Syntax) (ctorVal : ConstructorVal) (expectedType? : Option Expr) : TermElabM CtorHeaderResult := do
lvls ← ctorVal.lparams.mapM $ fun _ => mkFreshLevelMVar ref;
let val  := Lean.mkConst ctorVal.name lvls;
let type := (ConstantInfo.ctorInfo ctorVal).instantiateTypeLevelParams lvls;
r ← mkCtorHeaderAux ref ctorVal.nparams type val #[];
propagateExpectedType ref r.ctorFnType ctorVal.nfields expectedType?;
synthesizeAppInstMVars ref r.instMVars;
pure r

def markDefaultMissing (e : Expr) : Expr :=
mkAnnotation `structInstDefault e

def isDefaultMissing? (e : Expr) : Option Expr :=
isAnnotation? `structInstDefault e

def throwFailedToElabField {α} (ref : Syntax) (fieldName : Name) (structName : Name) (msgData : MessageData) : TermElabM α :=
throwError ref ("failed to elaborate field '" ++ fieldName ++ "' of '" ++ structName ++ ", " ++ msgData)

private partial def elabStruct : Struct → Option Expr → TermElabM (Expr × Struct)
| s, expectedType? => do
  env ← getEnv;
  let ctorVal := getStructureCtor env s.structName;
  { ctorFn := ctorFn, ctorFnType := ctorFnType, .. } ← mkCtorHeader s.ref ctorVal expectedType?;
  (e, _, fields) ← s.fields.foldlM
    (fun (acc : Expr × Expr × Fields) field =>
      let (e, type, fields) := acc;
      match field.lhs with
      | [FieldLHS.fieldName ref fieldName] => do
        type ← whnfForall field.ref type;
        match type with
        | Expr.forallE _ d b c =>
          let continue (val : Expr) (field : Field Struct) : TermElabM (Expr × Expr × Fields) := do {
            let e     := mkApp e val;
            let type  := b.instantiate1 val;
            let field := { expr? := some val, .. field };
            pure (e, type, field::fields)
          };
          match field.val with
          | FieldVal.term stx => do val ← elabTerm stx (some d); val ← ensureHasType stx d val; continue val field
          | FieldVal.nested s => do (val, sNew) ← elabStruct s (some d); val ← ensureHasType s.ref d val; continue val { val := FieldVal.nested sNew, .. field }
          | FieldVal.default  => do val ← mkFreshExprMVar field.ref (some d); continue (markDefaultMissing val) field
        | _ => throwFailedToElabField field.ref fieldName s.structName ("unexpected constructor type" ++ indentExpr type)
      | _ => throwError field.ref "unexpected unexpanded structure field")
    (ctorFn, ctorFnType, []);
  pure (e, s.setFields fields.reverse)

namespace DefaultFields

structure Context :=
-- We must search for default values overriden in derived structures
(structs : Array Struct := #[])
(allStructNames : Array Name := #[])
/-
Consider the following example:
```
structure A :=
(x : Nat := 1)

structure B extends A :=
(y : Nat := x + 1) (x := y + 1)

structure C extends B :=
(z : Nat := 2*y) (x := z + 3)
```
And we are trying to elaborate a structure instance for `C`. There are default values for `x` at `A`, `B`, and `C`.
We say the default value at `C` has distance 0, the one at `B` distance 1, and the one at `A` distance 2.
The field `maxDistance` specifies the maximum distance considered in a round of Default field computation.
Remark: since `C` does not set a default value of `y`, the default value at `B` is at distance 0.

The fixpoint for setting default values works in the following way.
- Keep computing default values using `maxDistance == 0`.
- We increase `maxDistance` whenever we failed to compute a new default value in a round.
- If `maxDistance > 0`, then we interrupt a round as soon as we compute some default value.
  We use depth-first search.
- We sign an error if no progress is made when `maxDistance` == structure hierarchy depth (2 in the example above).
-/
(maxDistance : Nat := 0)

structure State :=
(progress : Bool := false)

partial def collectStructNames : Struct → Array Name → Array Name
| struct, names =>
  let names := names.push struct.structName;
  struct.fields.foldl
    (fun names field =>
      match field.val with
      | FieldVal.nested struct => collectStructNames struct names
      | _ => names)
    names

partial def getHierarchyDepth : Struct → Nat
| struct =>
  struct.fields.foldl
    (fun max field =>
      match field.val with
      | FieldVal.nested struct => Nat.max max (getHierarchyDepth struct + 1)
      | _ => max)
    0

partial def findDefaultMissing? (mctx : MetavarContext) : Struct → Option (Field Struct)
| struct =>
  struct.fields.findSome? $ fun field =>
   match field.val with
   | FieldVal.nested struct => findDefaultMissing? struct
   | _ => match field.expr? with
     | none      => unreachable!
     | some expr => match isDefaultMissing? expr with
       | some (Expr.mvar mvarId _) => if mctx.isExprAssigned mvarId then none else some field
       | _                         => none

def getFieldName (field : Field Struct) : Name :=
match field.lhs with
| [FieldLHS.fieldName _ fieldName] => fieldName
| _ => unreachable!

abbrev M := ReaderT Context (StateT State TermElabM)

def isRoundDone : M Bool := do
ctx ← read;
s ← get;
pure (s.progress && ctx.maxDistance > 0)

def getFieldValue? (struct : Struct) (fieldName : Name) : Option Expr :=
struct.fields.findSome? $ fun field =>
  if getFieldName field == fieldName then
    field.expr?
  else
    none

partial def mkDefaultValueAux? (struct : Struct) : Expr → TermElabM (Option Expr)
| Expr.lam n d b c =>
  let ref := struct.ref;
  if c.binderInfo.isExplicit then
    let fieldName := n;
    match getFieldValue? struct fieldName with
    | none     => pure none
    | some val => do
      valType ← inferType ref val;
      condM (isDefEq ref valType d)
        (mkDefaultValueAux? (b.instantiate1 val))
        (pure none)
  else do
    arg ← mkFreshExprMVar ref d;
    mkDefaultValueAux? (b.instantiate1 arg)
| e =>
  if e.isAppOfArity `id 2 then
    pure (some e.appArg!)
  else
    pure (some e)

def mkDefaultValue? (struct : Struct) (cinfo : ConstantInfo) : TermElabM (Option Expr) := do
let ref := struct.ref;
us ← cinfo.lparams.mapM $ fun _ => mkFreshLevelMVar ref;
mkDefaultValueAux? struct (cinfo.instantiateValueLevelParams us)

/-- If `e` is a projection function of one of the given structures, then reduce it -/
def reduceProjOf? (structNames : Array Name) (e : Expr) : MetaM (Option Expr) := do
if !e.isApp then pure none
else match e.getAppFn with
  | Expr.const name _ _ => do
    env ← Meta.getEnv;
    if env.isProjectionFn name then
      match name with
      | Name.str structName fieldName _ => do
        if structNames.contains structName then
          Meta.unfoldDefinition? e
        else
          pure none
      | _ => pure none
    else
      pure none
  | _ => pure none

/-- Reduce default value. It performs beta reduction and projections of the given structures. -/
partial def reduce (structNames : Array Name) : Expr → MetaM Expr
| e@(Expr.lam _ _ _ _)     => Meta.lambdaTelescope e $ fun xs b => do b ← reduce b; Meta.mkLambda xs b
| e@(Expr.forallE _ _ _ _) => Meta.forallTelescope e $ fun xs b => do b ← reduce b; Meta.mkForall xs b
| e@(Expr.letE _ _ _ _ _)  => Meta.lambdaTelescope e $ fun xs b => do b ← reduce b; Meta.mkLambda xs b
| e@(Expr.proj _ i b _)    => do
  r? ← Meta.reduceProj? b i;
  match r? with
  | some r => reduce r
  | none   => do b ← reduce b; pure $ e.updateProj! b
| e@(Expr.app f _ _) => do
  r? ← reduceProjOf? structNames e;
  match r? with
  | some r => reduce r
  | none   => do
    let f := f.getAppFn;
    f' ← reduce f;
    if f'.isLambda then
      let revArgs := e.getAppRevArgs;
      reduce $ f'.betaRev revArgs
    else do
      args ← e.getAppArgs.mapM reduce;
      pure (mkAppN f' args)
| e@(Expr.mdata _ b _) => do
  b ← reduce b;
  if (isDefaultMissing? e).isSome && !b.isMVar then
    pure b
  else
    pure $ e.updateMData! b
| e@(Expr.mvar mvarId _) => do
  val? ← Meta.getExprMVarAssignment? mvarId;
  match val? with
  | some val => if val.isMVar then reduce val else pure val
  | none     => pure e
| e => pure e

partial def tryToSynthesizeDefaultAux (ref : Syntax) (structs : Array Struct) (allStructNames : Array Name) (maxDistance : Nat)
    (fieldName : Name) (mvarId : MVarId) : Nat → Nat → TermElabM Bool
| i, dist =>
  if dist > maxDistance then pure false
  else if h : i < structs.size then do
    let struct := structs.get ⟨i, h⟩;
    let defaultName := struct.structName ++ fieldName ++ `_default;
    env ← getEnv;
    match env.find? defaultName with
    | some cinfo@(ConstantInfo.defnInfo defVal) => do
      mctx ← getMCtx;
      val? ← mkDefaultValue? struct cinfo;
      match val? with
      | none     => do setMCtx mctx; tryToSynthesizeDefaultAux (i+1) (dist+1)
      | some val => do
        val ← liftMetaM struct.ref $ reduce allStructNames val;
        match val.find? $ fun e => (isDefaultMissing? e).isSome with
        | some _ => do setMCtx mctx; tryToSynthesizeDefaultAux (i+1) (dist+1)
        | none   => do
          mvarDecl ← getMVarDecl mvarId;
          val ← ensureHasType ref mvarDecl.type val;
          assignExprMVar mvarId val;
          pure true
    | _ => tryToSynthesizeDefaultAux (i+1) dist
  else
    pure false

def tryToSynthesizeDefault (ref : Syntax) (structs : Array Struct) (allStructNames : Array Name)
    (maxDistance : Nat) (fieldName : Name) (mvarId : MVarId) : TermElabM Bool :=
tryToSynthesizeDefaultAux ref structs allStructNames maxDistance fieldName mvarId 0 0

partial def step : Struct → M Unit
| struct => unlessM isRoundDone $ adaptReader (fun (ctx : Context) => { structs := ctx.structs.push struct, .. ctx }) $ do
  struct.fields.forM $ fun field =>
    match field.val with
    | FieldVal.nested struct => step struct
    | _ => match field.expr? with
      | none      => unreachable!
      | some expr => match isDefaultMissing? expr with
        | some (Expr.mvar mvarId _) =>
          unlessM (liftM $ isExprMVarAssigned mvarId) $ do
            ctx ← read;
            whenM (liftM $ tryToSynthesizeDefault field.ref ctx.structs ctx.allStructNames ctx.maxDistance (getFieldName field) mvarId) $ do
              modify $ fun s => { progress := true, .. s }
        | _ => pure ()

partial def propagateLoop (hierarchyDepth : Nat) : Nat → Struct → M Unit
| d, struct => do
  mctx ← liftM $ getMCtx;
  match findDefaultMissing? mctx struct with
  | none       => pure () -- Done
  | some field =>
    if d > hierarchyDepth then
      liftM $ throwError field.ref ("field '" ++ getFieldName field ++ "' is missing")
    else adaptReader (fun (ctx : Context) => { maxDistance := d, .. ctx }) $ do
      modify $ fun (s : State) => { progress := false, .. s};
      step struct;
      s ← get;
      if s.progress then do
        propagateLoop 0 struct
      else
        propagateLoop (d+1) struct

def propagate (struct : Struct) : TermElabM Unit :=
let hierarchyDepth := getHierarchyDepth struct;
let structNames := collectStructNames struct #[];
(propagateLoop hierarchyDepth 0 struct { allStructNames := structNames }).run' {}

end DefaultFields

private def elabStructInstAux (stx : Syntax) (expectedType? : Option Expr) (source : Source) : TermElabM Expr := do
structName ← getStructName stx expectedType? source;
env ← getEnv;
unless (isStructureLike env structName) $
  throwError stx ("invalid {...} notation, '" ++ structName ++ "' is not a structure");
struct ← expandStruct $ mkStructView stx structName source;
trace `Elab.struct stx $ fun _ => toString struct;
(r, struct) ← elabStruct struct expectedType?;
DefaultFields.propagate struct;
pure r

@[builtinTermElab structInst] def elabStructInst : TermElab :=
fun stx expectedType? => do
  stxNew? ← expandNonAtomicExplicitSource stx;
  match stxNew? with
  | some stxNew => withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?
  | none => do
    sourceView ← getStructSource stx;
    modifyOp?  ← isModifyOp? stx;
    match modifyOp?, sourceView with
    | some modifyOp, Source.explicit _ source => elabModifyOp stx modifyOp source expectedType?
    | some _,        _                        => throwError stx ("invalid {...} notation, explicit source is required when using '[<index>] := <value>'")
    | _,             _                        => elabStructInstAux stx expectedType? sourceView

end StructInst
end Term
end Elab
end Lean
