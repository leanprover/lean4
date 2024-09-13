/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Parser.Term
import Lean.Elab.Term
import Lean.Elab.Binders
import Lean.PrettyPrinter
import Lean.Data.Options
import Init.Data.Sum
import Lean.Meta.CollectFVars

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

/--
    Represents `ind params1 ... paramsn`, where `paramsi` is either a nested occurence, a constant name, or a free variable

    Example :
    ```
    inductive Foo (α β γ: Type) : Type → Type

    inductive Bar
        | foo : A -> B -> Foo A (Option Bar) B Nat → Bar

    ```
    this nested occurence `Foo A (Option Bar) B Nat` is encoded as
    ```lean
      node Foo #[
        .inr (.bvar 2),
        .inl (node Option #[.inr (.leaf Bar #[])]),
        .inr (.bvar 1),
        ]
    ```

    Remark 1 : Since an inductive can only be nested as a parameter, not an index, of another inductive type,
    we assume `params.size == ind.numParams`

    Remark 2 : Free variables are abstracted away as bound variables in nested occurences.
    This is useful when trying to delete duplicate occurences, since the check is now purely syntactical.
  -/
inductive NestedOccurence : Type :=
  | node (ind : InductiveVal) (params : Array (NestedOccurence ⊕ Expr))
  | leaf (ind : InductiveVal) (fvars : Array Expr)

namespace NestedOccurence

instance : Inhabited NestedOccurence := ⟨leaf default #[]⟩
instance : Inhabited (NestedOccurence ⊕ α) := ⟨.inl default⟩

partial instance : BEq NestedOccurence := ⟨go⟩
where go
  | leaf ind₁ _,.leaf ind₂ _ => ind₁.name == ind₂.name
  | node ind₁ arr₁,.node ind₂ arr₂ => Id.run do
    unless ind₁.name == ind₂.name && arr₁.size == arr₂.size do
      return false
    for i in [:arr₁.size] do
      unless @Sum.instBEq _ _ ⟨go⟩ inferInstance |>.beq arr₁[i]! arr₂[i]! do
        return false
    return true
  | _,_ => false

partial instance : ToString NestedOccurence := ⟨go⟩
where go
  | leaf ind e   => s!"leaf {ind.name} {e}"
  | node ind arr =>
    let s := arr.map (@instToStringSum _ _ ⟨go⟩ inferInstance |>.toString)
    s!"node {ind.name} {s}"

@[inline]
def getIndVal :  NestedOccurence → InductiveVal
  | leaf indVal _ | node indVal _ => indVal

@[inline]
def getArr :  NestedOccurence → Array (NestedOccurence ⊕ Expr)
  | leaf ..    => #[]
  | node _ arr => arr

@[inline]
def isLeaf : NestedOccurence → Bool
  | leaf .. => true
  | node .. => false

@[inline]
def isNode : NestedOccurence → Bool := not ∘ isLeaf

partial def containsFVar (fvarId : FVarId) : NestedOccurence → Bool
  | leaf _ e   => e.any (Expr.containsFVar · fvarId)
  | node _ arr => arr.any (Sum.elim (containsFVar fvarId) (Expr.containsFVar · fvarId))

partial def toListofNests (e : NestedOccurence) : List NestedOccurence :=
  match e with
  | .leaf _ _   => []
  | .node _ arr =>
    let l := flip arr.foldr [] fun occ l =>
      if let .inl occ := occ then
          occ.toListofNests ++ l
      else l
    e::l

/-- Return the inductive declaration's type applied to the arguments in `argNames`. -/
partial def mkAppTerm (nestedOcc : NestedOccurence) (argNames : Array Name) : TermElabM Term := do
  go nestedOcc argNames
where
  go (nestedOcc : NestedOccurence) (argNames : Array Name) : TermElabM Term := do
  match nestedOcc with
    | leaf indVal _ =>
      let f := mkCIdent indVal.name
      let numArgs := indVal.numParams + indVal.numIndices
      unless argNames.size >= numArgs do
          throwError s!"Expected {numArgs} arguments for {indVal.name}, got {argNames}"
      let mut args := Array.mkArray numArgs default
      for i in [:numArgs] do
        let arg := mkIdent argNames[i]!
        args := args.set! i arg
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

/-- Return the inductive declaration's type applied to the arguments in `argNames`. -/
partial def mkAppExpr (nestedOcc : NestedOccurence) (argNames : Array Expr) : TermElabM Expr := do
  let res ← go nestedOcc argNames
  return res
where
  go (nestedOcc : NestedOccurence) (argNames : Array Expr): TermElabM Expr := do
  match nestedOcc with
    | leaf indVal _ =>
      let numArgs := indVal.numParams + indVal.numIndices
      unless argNames.size >= numArgs do
          throwError s!"Expected {numArgs} arguments for {indVal.name}, got {argNames}"
      let mut args := Array.mkArray numArgs default
      for i in [:numArgs] do
        let arg := argNames[i]!
        args := args.modify i (fun _ => arg)
      let name ← Meta.mkConstWithFreshMVarLevels indVal.name
      let res := args.foldl mkApp name
      return res
    | node indVal arr =>
      let mut args := #[]
      for nestedOcc? in arr do
        match nestedOcc? with
          | .inl occ =>
            let arg ← go occ argNames
            args := args.push arg
          | .inr (.bvar i) =>
            let some argName := argNames[argNames.size-i-1]?
              | throwError s!"Cannot instantiate {nestedOcc} : not enough arguments given"
            args := args.push argName
          | .inr e =>
            args := args.push e
      let res ← Meta.mkAppOptM indVal.name (args.map some)
      return res

structure Result where
  occ : NestedOccurence
  args : Subarray Expr
  argNames : Array Name

instance : ToString Result where
  toString res := s!"⟨{res.occ},{res.args},{res.argNames}⟩"

instance : BEq Result := ⟨(·.occ == ·.occ)⟩

structure Context where
  indNames : List Name
  results : List Result

end NestedOccurence

abbrev NestedOccM := StateT NestedOccurence.Context TermElabM

def withIndNames (indNames : List Name) (f : NestedOccM Unit) : TermElabM NestedOccurence.Context := do
  let ⟨(),ctx⟩ ← StateT.run f ⟨indNames,[]⟩
  return ctx

def addResult (x : NestedOccurence.Result) : NestedOccM Unit := do
  let ⟨names,res⟩ ← get
  set (⟨names,x::res⟩ : NestedOccurence.Context)

def addName (n : Name) : NestedOccM Unit := do
  let ⟨names,res⟩ ← get
  set (⟨n::names,res⟩ : NestedOccurence.Context)

partial def getNestedOccurencesOf (inds : List Name) (e: Expr) (fvars : Array Expr): MetaM (Option NestedOccurence) := do
  let .inl occs ← go e | return none
  return occs
where
  go (e : Expr) : MetaM (NestedOccurence ⊕ Expr) := do
    let hd := e.getAppFn
    let args := e.getAppArgs
    let fallback _ := return .inr <| e.abstract fvars
    let .const name _ := hd | fallback ()
    if let some indName := inds.find? (· = name) then
      let indVal ← getConstInfoInduct indName
      let args := args.map (Expr.instantiateRev · fvars)
      return .inl <| .leaf indVal args
    else
      try
        let indVal ← getConstInfoInduct name
        let args := args.map (Expr.abstract  · fvars)
        let nestedOccsArgs ← args.mapM go
        if nestedOccsArgs.any (· matches .inl _) then
          return .inl <| .node indVal nestedOccsArgs
        else fallback ()
      catch _ => fallback ()

partial def getNestedOccurences (indNames : List Name) : TermElabM (List NestedOccurence.Result) := do
  let ⟨_,l⟩ ← withIndNames indNames do
    for name in indNames do
      go name #[] #[]
  return l.eraseDups
where
  go (indName : Name) (args : Array Expr) (fvars : Array Expr): NestedOccM Unit := do
    let indVal ← getConstInfoInduct indName
    if !indVal.isNested && args.size == 0 then
      return
    let consts ← indVal.ctors.mapM getConstInfoCtor
    for constInfo in consts do
      let instConstInfo ← forallBoundedTelescope constInfo.type args.size fun xs e =>
        return e.abstract xs |>.instantiateRev args
      forallTelescope instConstInfo fun xs _ => do
        let mut paramArgs ← fvars.mapM fun e => do
          let localDecl ← e.fvarId!.getDecl
          mkFreshUserName localDecl.userName.eraseMacroScopes
        let mut l := []
        for i in [:constInfo.numParams - args.size] do
          let some e := xs[i]? | break
          let localDecl ← e.fvarId!.getDecl
          let paramName ← mkFreshUserName localDecl.userName.eraseMacroScopes
          paramArgs := paramArgs.push paramName
        let mut localArgs := #[]
        for i in [:xs.size] do
          let e := xs[i]!
          let ty ← e.fvarId!.getType
          let localDecl ← e.fvarId!.getDecl
          let paramName ← mkFreshUserName localDecl.userName.eraseMacroScopes
          let occs ← getNestedOccurencesOf indNames ty xs[:i]
          let l' := if let .some x := occs then x.toListofNests else []
          for occ in l' do
            let new_args := paramArgs ++ localArgs.filter (occ.containsFVar ⟨·⟩)
            if (← get).results.all (occ != ·.occ) then
              addResult ⟨occ, xs[:i], new_args⟩
              let fvars := fvars ++ xs[:i]
              let app   ← occ.mkAppExpr fvars
              let hd    := app.getAppFn.constName!
              let args  := app.getAppArgs
              addName hd
              go hd args fvars
            else
              addResult ⟨occ,xs[:i],new_args⟩
          l := l ++ l'
          localArgs := localArgs.push paramName

def indNameToFunName (indName : Name) : String  :=
  match indName.eraseMacroScopes with
    | .str _ t => t
    | _ => "instFn"

partial def mkInstName: NestedOccurence → String
  | .leaf ind _ => indNameToFunName ind.name
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
where
  go (nestedOcc : NestedOccurence) (argNames : Array Name) : TermElabM (Array Syntax) :=
  let indVal := nestedOcc.getIndVal
  let arr    := nestedOcc.getArr
  forallBoundedTelescope indVal.type indVal.numParams fun xs _ => do
    let mut binders : Array Syntax := #[]
    for i in [:xs.size] do
      if nestedOcc.isNode && arr[i]? matches some (.inl _) then
        let some occ := arr[i]!.getLeft? | unreachable!
        let nestedBinders ← go occ argNames
        binders := binders ++ nestedBinders
      else try
          let x := xs[i]!
          let hd ← mkConstWithFreshMVarLevels className
          let c := mkAppN hd #[x]
          if (← isTypeCorrect c) then
            let some argName := argNames[i]? | pure ()
            let binder ← `(instBinderF| [$(mkCIdent className) $(mkIdent argName)])
            binders := binders.push binder
        catch _ => pure ()
    return binders

structure Context : Type where
  indNames    : List Name
  typeArgNames: Array (Array Name)
  typeInfos   : Array NestedOccurence
  auxFunNames : Array Name
  usePartial  : Bool

def mkContext (fnPrefix : String) (typeName : Name) (withNested : Bool := true): TermElabM Context := do
  let indVal ← getConstInfoInduct typeName
  let indNames := indVal.all
  let mut typeInfos' : List NestedOccurence.Result := []
  for indName in indNames do
    let indVal ← getConstInfoInduct indName
    let args ← mkInductArgNames indVal
    typeInfos' := ⟨.leaf indVal #[], #[].toSubarray, args⟩::typeInfos'
  if withNested then
    typeInfos' := (← getNestedOccurences indVal.all) ++ typeInfos'
  let typeArgNames := typeInfos'.map (·.argNames) |>.toArray
  let typeInfos := typeInfos'.map (·.occ) |>.toArray
  let auxFunNames ← typeInfos.mapM fun occ => do
    return ← mkFreshUserName <| Name.mkSimple <| fnPrefix ++ mkInstName occ
  let usePartial := !withNested && indVal.isNested
  return {indNames, typeArgNames, typeInfos, auxFunNames, usePartial}

def mkLocalInstanceLetDecls (ctx : Context) (className : Name) (argNames : Array Name) : TermElabM (Array (TSyntax ``Parser.Term.letDecl)) := do
  let mut letDecls := #[]
  for i in [:ctx.typeInfos.size] do
    let occ          := ctx.typeInfos[i]!
    let auxFunName   := ctx.auxFunNames[i]!
    unless occ.isLeaf do
      continue
    let indVal       := occ.getIndVal
    let currArgNames ← mkInductArgNames indVal
    let numParams    := indVal.numParams
    let currIndices  := currArgNames[numParams:]
    let binders      ← mkImplicitBinders currIndices
    let argNamesNew  := argNames[:numParams] ++ currIndices
    let indType      ← mkInductiveApp indVal argNamesNew
    let type         ← `($(mkCIdent className) $indType)
    let val          ← `(⟨$(mkIdent auxFunName)⟩)
    let instName     ← mkFreshUserName `localinst
    let letDecl      ← `(Parser.Term.letDecl| $(mkIdent instName):ident $binders:implicitBinder* : $type := $val)
    letDecls := letDecls.push letDecl
  return letDecls

def mkLet (letDecls : Array (TSyntax ``Parser.Term.letDecl)) (body : Term) : TermElabM Term :=
  letDecls.foldrM (init := body) fun letDecl body =>
    `(let $letDecl:letDecl; $body)

open TSyntax.Compat in
def mkInstanceCmds (ctx : Context) (className : Name) (useAnonCtor := true) : TermElabM (Array Command) := do
  let mut instances := #[]
  for i in [:ctx.typeInfos.size] do
    let nestedOcc  := ctx.typeInfos[i]!
    unless nestedOcc.isLeaf do continue
    let auxFunName := ctx.auxFunNames[i]!
    let argNames   := ctx.typeArgNames[i]!
    let binders    ←  mkImplicitBinders argNames
    let binders    := binders ++ (← mkInstImplicitBinders className nestedOcc argNames)
    let indType    ←  nestedOcc.mkAppTerm argNames
    let type       ←  `($(mkCIdent className) $indType)
    let mut val    := mkIdent auxFunName
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
  let mut binders ← mkImplicitBinders argNames
  let targetType  ← nestedOcc.mkAppTerm argNames
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
