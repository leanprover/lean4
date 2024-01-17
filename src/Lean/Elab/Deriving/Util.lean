/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Parser.Term
import Lean.Elab.Term
import Lean.Elab.Binders
import Lean.PrettyPrinter
import Lean.Data.Options

namespace Lean.Elab.Deriving
open Meta

def implicitBinderF := Parser.Term.implicitBinder
def instBinderF     := Parser.Term.instBinder
def explicitBinderF := Parser.Term.explicitBinder

/-- Make fresh, hygienic names for every parameter and index of an inductive declaration.

For example, `inductive Foo {α : Type} : Nat → Type` will give something like ``#[`α✝, `a✝]``. -/
def mkInductArgNames (indVal : InductiveVal) : TermElabM (Array Name) := do
  forallTelescopeReducing indVal.type fun xs _ => do
    let mut argNames := #[]
    for x in xs do
      let localDecl ← x.fvarId!.getDecl
      let paramName ← mkFreshUserName localDecl.userName.eraseMacroScopes
      argNames := argNames.push paramName
    pure argNames

/-- Return the inductive declaration's type applied to the arguments in `argNames`. -/
def mkInductiveApp (indVal : InductiveVal) (argNames : Array Name) : TermElabM Term :=
  let f    := mkCIdent indVal.name
  let args := argNames.map mkIdent
  `(@$f $args*)

open TSyntax.Compat in
/-- Return implicit binder syntaxes for the given `argNames`. The output matches `implicitBinder*`.

For example, ``#[`foo,`bar]`` gives `` `({foo} {bar})``. -/
def mkImplicitBinders (argNames : Array Name) : TermElabM (Array (TSyntax ``Parser.Term.implicitBinder)) := do
  argNames.mapM fun argName =>
    `(implicitBinderF| { $(mkIdent argName) })

inductive NestedOccurence : Type :=
/--
    Represents `ind params1 ... paramsn`, where `paramsi` is either a nested occurence, a constant name, or a free variable

    Example :
    ```
    inductive Foo (α β γ: Type) : Type → Type

    inductive Bar
        | foo : A -> B -> Foo A (Option Bar) B Nat → Bar

    ```,
    this nested occurence `Foo A (Option Bar) B Nat` is encoded as
    ```lean
      node Foo #[
        .inr (.bvar 2),
        .inl (node Option #[.inr (.leaf Bar)]),
        .inr (.bvar 1),
        ]
    ```

    Remark 1 : Since an inductive can only be nested as a parameter, not an index, of another inductive type,
    we assume `params.size == ind.numParams`

    Remark 2 : Free variables are abstracted away in nested occurences.
    This is useful when trying to delete duplicate occurences, since the check is now purely syntactical.
  -/
  | node (ind : InductiveVal) (params : Array (NestedOccurence ⊕ Expr))
  | leaf (ind : InductiveVal)

namespace NestedOccurence

instance : Inhabited NestedOccurence := ⟨leaf default⟩
partial instance : BEq NestedOccurence := ⟨go⟩
where go
      | leaf ind₁,.leaf ind₂ => ind₁.name == ind₂.name
      | node ind₁ arr₁,.node ind₂ arr₂ => Id.run do
        unless ind₁.name == ind₂.name && arr₁.size == arr₂.size  do
          return false
        for i in [:arr₁.size] do
          unless @instBEqSum _ _ ⟨go⟩ inferInstance|>.beq arr₁[i]! arr₂[i]! do
            return false
        return true
      | _,_ => false

partial instance : ToString NestedOccurence := ⟨go⟩
where go
      | leaf ind => s!"leaf {ind.name}"
      | node ind arr =>
        let s := arr.map (@instToStringSum _ _ ⟨go⟩ ⟨reprStr⟩ |>.toString)
        s!"node {ind.name} {s}"

@[inline]
def getIndVal :  NestedOccurence → InductiveVal
  | leaf indVal | node indVal _ => indVal

def getArr :  NestedOccurence → Array (NestedOccurence ⊕ Expr)
  | leaf _ => #[]
  | node _ arr => arr

@[inline]
def isLeaf : NestedOccurence → Bool
  | leaf _ => true
  | node .. => false

@[inline]
def isNode : NestedOccurence → Bool := not ∘ isLeaf

partial def containsFVar (fvarId : FVarId) : NestedOccurence → Bool
  | leaf _ => false
  | node _ arr => arr.any (Sum.lift (containsFVar fvarId) (Expr.containsFVar · fvarId))

partial def toListofNests (e : NestedOccurence) : List NestedOccurence :=
  match e with
  | .leaf _ => []
  | .node _ arr =>
    let l := flip arr.foldr [] fun occ l =>
      if let .inl occ := occ then
          occ.toListofNests ++ l
      else l
    e::l

/-- Return the inductive declaration's type applied to the arguments in `argNames`. -/
partial def mkAppN (nestedOcc : NestedOccurence) (argNames : Array Name) : TermElabM Term := do
  go nestedOcc argNames
where
  go (nestedOcc : NestedOccurence) (argNames : Array Name) : TermElabM Term := do
  match nestedOcc with
    | leaf indVal => do
      let f := mkCIdent indVal.name
      let numArgs := indVal.numParams + indVal.numIndices
      unless argNames.size >= numArgs do
          throwError s!"Expected {numArgs} arguments for {indVal.name}, got {argNames}"
      let mut args := Array.mkArray numArgs default
      for i in [:numArgs] do
        let arg := mkIdent argNames[i]!
        args := args.modify i (λ _ => arg)
      `(@$f $args*)
    | node indVal arr =>
      let f := mkCIdent indVal.name
      let mut args := #[]
      for nestedOcc? in arr do
        match nestedOcc? with
          | .inl occ =>
            let arg ← go occ argNames
            args := args.push arg
          | .inr (.bvar i) =>
            let some argName := argNames[argNames.size-i-1]?
              | throwError s!"Cannot instantiate {nestedOcc} : not enough arguments given"
            let id := mkIdent argName
            args   := args.push <| ←`($id)
          | .inr e =>
            let tm ← PrettyPrinter.delab e
            args := args.push <| ←`($tm)
      `(@$f $args*)

end NestedOccurence

partial def getNestedOccurencesOf (inds : List Name) (e: Expr) (fvars : Subarray Expr): MetaM (Option NestedOccurence) := do
  let .inl occs ← go e | return none
  return occs
where
  go (e : Expr) : MetaM (NestedOccurence ⊕ Expr) := do
    let hd := e.getAppFn
    let fallback _ := pure <| .inr <| e.abstract fvars
    let  .const name .. := hd | fallback ()
    if let some indName := inds.find? (· = name) then
      let indVal ← getConstInfoInduct indName
      return .inl <| .leaf indVal
    else
      try
        let indVal ← getConstInfoInduct name
        let args := e.getAppArgs
        let args := args.map (·.abstract fvars)
        let nestedOccsArgs ← args.mapM <| go
        if nestedOccsArgs.any Sum.isLeft then
          return .inl <| .node indVal nestedOccsArgs
        else fallback ()
      catch _ => fallback ()

def getNestedOccurences (indNames : List Name) : TermElabM (List (Array Name × NestedOccurence)) := do
  let l ← indNames.foldlM (fun l x => bind (go x) (return · ++ l)) []
  -- We erase duplicates up to alpha-equivalence
  return @List.eraseDups _ (⟨fun ⟨_,occ₁⟩ ⟨_,occ₂⟩=> BEq.beq occ₁ occ₂⟩) l
  where
  go (indName : Name) := do
    let indVal ← getConstInfoInduct indName
    if !indVal.isNested then
      return []
    let constrs ← indVal.ctors.mapM (getConstInfoCtor)
    let mut res := []
    for constInfo in constrs do
      let constList ← forallTelescope constInfo.type fun xs _ => do
        let mut paramArgs := #[]
        let mut l := []
        for i in [:constInfo.numParams] do
          let e := xs[i]!
          let localDecl ← e.fvarId!.getDecl
          let paramName ← mkFreshUserName localDecl.userName.eraseMacroScopes
          paramArgs := paramArgs.push paramName
        let mut localArgs := #[]
        for i in [constInfo.numParams:xs.size] do
          let e := xs[i]!
          let ty ← e.fvarId!.getType
          let localDecl ← e.fvarId!.getDecl
          let paramName ← mkFreshUserName localDecl.userName.eraseMacroScopes
          let occs ← getNestedOccurencesOf indNames ty xs[:i]
          let l' := if let .some x := occs then x.toListofNests else []
          let l' := l'.map fun occ =>
            let relevantLocalArgs := localArgs.filter (occ.containsFVar ⟨·⟩)
            let args := paramArgs ++ relevantLocalArgs
            (args,occ)
          l := l ++ l'
          localArgs := localArgs.push paramName
        pure l
      res := res ++ constList
    return res

def indNameToFunName (indName : Name) : String  :=
  match indName.eraseMacroScopes with
    | .str _ t => t
    | _ => "instFn"

partial def mkInstName: NestedOccurence → String
  | .leaf ind => indNameToFunName ind.name
  | .node ind arr => Id.run do
    let mut res ← indNameToFunName ind.name
    for nestedOcc in arr do
      if let .inl occ := nestedOcc then
        let nestedInstName ← mkInstName occ
        res := res ++ nestedInstName
    return res

/-- Return instance binder syntaxes binding `className α` for every generic parameter `α`
of the inductive `indVal` for which such a binding is type-correct. `argNames` is expected
to provide names for the parameters (see `mkInductArgNames`). The output matches `instBinder*`.

For example, given `inductive Foo {α : Type} (n : Nat) : (β : Type) → Type`, where `β` is an index,
invoking ``mkInstImplicitBinders `BarClass foo #[`α, `n, `β]`` gives `` `([BarClass α])``. -/
partial def mkInstImplicitBinders (className : Name) (nestedOcc : NestedOccurence) (argNames : Array Name) : TermElabM (Array Syntax) := do
  go nestedOcc argNames
  --sometimes generates duplicates, TODO fix
where
  go (nestedOcc : NestedOccurence) (argNames : Array Name) : TermElabM (Array Syntax) :=
  let indVal := nestedOcc.getIndVal
  let arr := nestedOcc.getArr
  forallBoundedTelescope indVal.type indVal.numParams fun xs _ => do
    let mut binders : Array Syntax := #[]
    for i in [:xs.size] do
      if nestedOcc.isNode && arr[i]? matches some (.inl _) then
        let occ := arr[i]!.getLeft!
        let nestedBinders ← go occ argNames
        binders := binders ++ nestedBinders
      else
        try
          let x := xs[i]!
          let c ← mkAppM className #[x]
          if (← isTypeCorrect c) then
            let some argName := argNames[i]? | pure ()
            let binder ← `(instBinderF| [ $(mkCIdent className) $(mkIdent argName)])
            binders := binders.push binder
        catch _ =>
          pure ()
    return binders

structure Context : Type where
  indNames    : List Name
  typeArgNames: Array (Array Name)
  typeInfos   : Array NestedOccurence
  auxFunNames : Array Name

def mkContext (fnPrefix : String) (typeName : Name) : TermElabM Context := do
  let indVal ← getConstInfoInduct typeName
  let indNames := indVal.all
  let mut typeInfos' := []
  for indName in indNames do
    let indVal ← getConstInfoInduct indName
    let args ← mkInductArgNames indVal
    typeInfos' := (args,.leaf indVal)::typeInfos'
  typeInfos' := (← getNestedOccurences indVal.all) ++ typeInfos'
  let typeArgNames := typeInfos'.map Prod.fst |>.toArray
  let typeInfos := typeInfos'.map Prod.snd |>.toArray
  trace[Elab.Deriving] s!"typeInfos : {typeInfos}\nargNames : {typeArgNames}"
  let auxFunNames ← typeInfos.mapM <|
    fun occ => do return ← mkFreshUserName <| Name.mkSimple <| fnPrefix ++ mkInstName occ
  return {
    indNames    := indNames
    typeArgNames:= typeArgNames
    typeInfos   := typeInfos
    auxFunNames := auxFunNames
  }

def mkLet (letDecls : Array (TSyntax ``Parser.Term.letDecl)) (body : Term) : TermElabM Term :=
  letDecls.foldrM (init := body) fun letDecl body =>
    `(let $letDecl:letDecl; $body)

open TSyntax.Compat in
def mkInstanceCmds (ctx : Context) (className : Name) (useAnonCtor := true) : TermElabM (Array Command) := do
  let mut instances := #[]
  for i in [:ctx.typeInfos.size] do
    let nestedOcc    := ctx.typeInfos[i]!
    unless nestedOcc.isLeaf do
      continue
    let auxFunName   := ctx.auxFunNames[i]!
    let argNames     := ctx.typeArgNames[i]!
    let binders      ← mkImplicitBinders argNames
    let binders      := binders ++ (← mkInstImplicitBinders className nestedOcc argNames)
    let indType      ← nestedOcc.mkAppN argNames
    let type         ← `($(mkCIdent className) $indType)
    let mut val      := mkIdent auxFunName
    if useAnonCtor then
      val ← `(⟨$val⟩)
    let instCmd ← `(instance $binders:implicitBinder* : $type := $val)
    instances := instances.push instCmd
  return instances

def mkDiscr (varName : Name) : TermElabM (TSyntax ``Parser.Term.matchDiscr) :=
 `(Parser.Term.matchDiscr| $(mkIdent varName):term)

structure Header where
  binders     : Array (TSyntax ``Parser.Term.bracketedBinder)
  argNames    : Array Name
  targetNames : Array Name
  targetType  : Term

open TSyntax.Compat in
def mkHeader (className : Name) (arity : Nat) (argNames : Array Name) (nestedOcc : NestedOccurence) : TermElabM Header := do
  let mut binders      ← mkImplicitBinders argNames
  let targetType       ← nestedOcc.mkAppN argNames
  let mut targetNames := #[]
  for _ in [:arity] do
    targetNames := targetNames.push (← mkFreshUserName `x)
  binders := binders ++ (← mkInstImplicitBinders className nestedOcc argNames)
  binders := binders ++ (← targetNames.mapM fun targetName => `(explicitBinderF| ($(mkIdent targetName) : $targetType)))
  return {
    binders     := binders
    argNames    := argNames
    targetNames := targetNames
    targetType  := targetType
  }

def mkDiscrs (header : Header) (indVal : InductiveVal) : TermElabM (Array (TSyntax ``Parser.Term.matchDiscr)) := do
  let mut discrs := #[]
  -- add indices
  for argName in header.argNames[indVal.numParams:] do
    discrs := discrs.push (← mkDiscr argName)
  return discrs ++ (← header.targetNames.mapM mkDiscr)

def Context.getFunName? (ctx : Context) (header : Header) (ty : Expr) (xs : Array Expr): TermElabM (Option Name) := do
      let indValNum ← ctx.typeInfos.findIdxM? <|
        (return .some · == (← getNestedOccurencesOf ctx.indNames ty xs[:header.argNames.size]))
      let recField := indValNum.map (ctx.auxFunNames[·]!)
      return recField

end Lean.Elab.Deriving
