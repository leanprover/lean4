import Lean

mutual

inductive Vect (α : Type u) (β : Type v) : Nat → Nat → Type max u v where
  | nil   : Vect α β 0 0
  | lst   : List (Array (Vect α β 0 0)) → Vect α β 0 0
  | cons1 : {n m : Nat} → TreeV α β n → Vect α β n m → Vect α β (n+1) m
  | cons2 : {n m : Nat} → TreeV α β m → Vect α β n m → Vect α β n (m+1)

inductive TreeV (α : Type u) (β : Type v) : Nat → Type max u v where
  | diag   : {n : Nat}   → Vect α β n n → TreeV α β n
  | lower  : {n m : Nat} → n < m → Vect α β n m → TreeV α β m

end

mutual

partial def aux1 {α β m n} [ToString α] [ToString β] (s : Vect α β m n) : String :=
  let inst1 {m' n' : Nat} : ToString (Vect α β m' n') := ⟨aux1⟩
  let inst1 {n' : Nat}    : ToString (TreeV α β n')   := ⟨aux2⟩
  match m, n, s with
  | _, _, Vect.nil       => "nil"
  | _, _, Vect.lst xs    => "lst " ++ toString xs
  | _, _, Vect.cons1 t v => "cons1 " ++ toString t ++ " " ++ toString v
  | _, _, Vect.cons2 t v => "cons2 " ++ toString t ++ " " ++ toString v


partial def aux2 {α β n} [ToString α] [ToString β] (s : TreeV α β n) : String :=
  let inst1 {m' n' : Nat} : ToString (Vect α β m' n') := ⟨aux1⟩
  let inst1 {n' : Nat}    : ToString (TreeV α β n')   := ⟨aux2⟩
  match n, s with
  | _, TreeV.diag v    => "diag  " ++ toString v
  | _, TreeV.lower _ v => "lower " ++ "<proof>" ++ " " ++ toString v

end

instance {α β m n} [ToString α] [ToString β] : ToString (Vect α β m n) where
  toString := aux1

instance {α β n} [ToString α] [ToString β] : ToString (TreeV α β n) where
  toString := aux2


namespace Test
mutual
inductive Foo (α : Type) where
  | mk : List (Bla α) → Foo α
  | leaf : α → Foo α
inductive Bla (α : Type) where
  | nil : Bla α
  | cons : Foo α → Bla α → Bla α
end


open Lean
open Lean.Meta

def tst : MetaM Unit := do
  let info ← getConstInfoInduct `Test.Bla
  trace[Meta.debug] "nested: {info.isNested}"
  pure ()

#eval tst

mutual

partial def fooToString {α : Type} [ToString α] (s : Foo α) : String :=
  let inst1 : ToString (Bla α) := ⟨blaToString⟩
  match s with
  | Foo.mk bs  => "Foo.mk " ++ toString bs
  | Foo.leaf a => "Foo.leaf " ++ toString a

partial def blaToString {α : Type} [ToString α] (s : Bla α) : String :=
  let inst1 : ToString (Bla α) := ⟨blaToString⟩
  let inst2 : ToString (Foo α) := ⟨fooToString⟩
  match s with
  | Bla.nil      => "Bla.nil"
  | Bla.cons h t => "Bla.cons (" ++ toString h ++ ") " ++ toString t

end

instance [ToString α] : ToString (Foo α) where
  toString := fooToString

instance [ToString α] : ToString (Bla α) where
  toString := blaToString

#eval Foo.mk [Bla.cons (Foo.leaf 10) Bla.nil]

end Test


namespace Lean.Elab
open Meta

namespace Deriving

/- For type classes such as BEq, ToString, Format -/
namespace Default

structure ContextCore where
  classInfo   : ConstantInfo
  typeInfos   : Array InductiveVal
  auxFunNames : Array Name
  usePartial  : Bool
  resultType  : Syntax

structure Header where
  binders    : Array Syntax
  argNames   : Array Name
  targetName : Name

abbrev MkAltRhs :=
  ContextCore → (ctorName : Name) → (ctorArgs : Array (Syntax × Expr)) → TermElabM Syntax

structure Context extends ContextCore where
  mkAltRhs : MkAltRhs

def mkContext (className : Name) (typeName : Name) (resultType : Syntax) (mkAltRhs : MkAltRhs) : TermElabM Context := do
  let indVal ← getConstInfoInduct typeName
  let mut typeInfos := #[]
  for typeName in indVal.all do
    typeInfos ← typeInfos.push (← getConstInfoInduct typeName)
  let classInfo ← getConstInfo className
  let mut auxFunNames := #[]
  for typeName in indVal.all do
    match className.eraseMacroScopes, typeName.eraseMacroScopes with
    | Name.str _ c _, Name.str _ t _ => auxFunNames := auxFunNames.push (← mkFreshUserName <| Name.mkSimple <| c.decapitalize ++ t)
    | _, _ => auxFunNames := auxFunNames.push (← mkFreshUserName `instFn)
  trace[Meta.debug] "{auxFunNames}"
  let usePartial := indVal.isNested || typeInfos.size > 1
  return {
    classInfo   := classInfo
    typeInfos   := typeInfos
    auxFunNames := auxFunNames
    usePartial  := usePartial
    resultType  := resultType
    mkAltRhs    := mkAltRhs
  }

def mkInductArgNames (indVal : InductiveVal) : TermElabM (Array Name) := do
  forallTelescopeReducing indVal.type fun xs _ => do
    let mut argNames := #[]
    for x in xs do
      let localDecl ← getLocalDecl x.fvarId!
      let paramName ← mkFreshUserName localDecl.userName.eraseMacroScopes
      argNames := argNames.push paramName
    pure argNames

def mkInductiveApp (indVal : InductiveVal) (argNames : Array Name) : TermElabM Syntax :=
  let f    := mkIdent indVal.name
  let args := argNames.map mkIdent
  `(@$f $args*)

def implicitBinderF := Parser.Term.implicitBinder
def instBinderF     := Parser.Term.instBinder
def explicitBinderF := Parser.Term.explicitBinder

def mkImplicitBinders (argNames : Array Name) : TermElabM (Array Syntax) :=
  argNames.mapM fun argName =>
    `(implicitBinderF| { $(mkIdent argName) })

def mkInstImplicitBinders (ctx : Context) (indVal : InductiveVal) (argNames : Array Name) : TermElabM (Array Syntax) :=
  forallBoundedTelescope indVal.type indVal.nparams fun xs _ => do
    let mut binders := #[]
    for i in [:xs.size] do
      try
        let x := xs[i]
        let clsName := ctx.classInfo.name
        let c ← mkAppM clsName #[x]
        if (← isTypeCorrect c) then
          let argName := argNames[i]
          let binder ← `(instBinderF| [ $(mkIdent clsName):ident $(mkIdent argName):ident ])
          binders := binders.push binder
      catch _ =>
        pure ()
    return binders

def mkHeader (ctx : Context) (indVal : InductiveVal) : TermElabM Header := do
  let argNames     ← mkInductArgNames indVal
  let binders      ← mkImplicitBinders argNames
  let targetType   ← mkInductiveApp indVal argNames
  let targetName   ← mkFreshUserName `x
  let targetBinder ← `(explicitBinderF| ($(mkIdent targetName) : $targetType))
  let binders      := binders ++ (← mkInstImplicitBinders ctx indVal argNames)
  let binders      := binders.push targetBinder
  return {
    binders    := binders
    argNames   := argNames
    targetName := targetName
  }

def mkLocalInstanceLetDecls (ctx : Context) (argNames : Array Name) : TermElabM (Array Syntax) := do
  let mut letDecls := #[]
  for i in [:ctx.typeInfos.size] do
    let indVal       := ctx.typeInfos[i]
    let auxFunName   := ctx.auxFunNames[i]
    let currArgNames ← mkInductArgNames indVal
    let numParams    := indVal.nparams
    let currIndices  := currArgNames[numParams:]
    let binders      ← mkImplicitBinders currIndices
    let argNamesNew  := argNames[:numParams] ++ currIndices
    let indType      ← mkInductiveApp indVal argNamesNew
    let type         ← `($(mkIdent ctx.classInfo.name) $indType)
    let val          ← `(⟨$(mkIdent auxFunName)⟩)
    let instName     ← mkFreshUserName `localinst
    let letDecl      ← `(Parser.Term.letDecl| $(mkIdent instName):ident $binders:implicitBinder* : $type := $val)
    letDecls := letDecls.push letDecl
  return letDecls

def mkLet (letDecls : Array Syntax) (body : Syntax) : TermElabM Syntax :=
  letDecls.foldrM (init := body) fun letDecl body =>
    `(let $letDecl:letDecl; $body)

def matchAltExpr := Parser.Term.matchAlt

def mkMatch (ctx : Context) (header : Header) (indVal : InductiveVal) (argNames : Array Name) : TermElabM Syntax := do
  let discrs ← mkDiscrs
  let alts ← mkAlts
  `(match $[$discrs],* with | $[$alts:matchAlt]|*)
where
  mkDiscr (varName : Name) : TermElabM Syntax :=
    `(Parser.Term.matchDiscr| $(mkIdent varName):term)

  mkDiscrs : TermElabM (Array Syntax) := do
    let mut discrs := #[]
    -- add indices
    for argName in argNames[indVal.nparams:] do
      discrs := discrs.push (← mkDiscr argName)
    return discrs.push (← mkDiscr header.targetName)

  mkAlts : TermElabM (Array Syntax) := do
    let mut alts := #[]
    for ctorName in indVal.ctors do
      let mut patterns := #[]
      -- add `_` pattern for indices
      for i in [:indVal.nindices] do
        patterns := patterns.push (← `(_))
      let ctorInfo ← getConstInfoCtor ctorName
      let mut ctorArgs := #[]
      -- add `_` for inductive parameters, they are inaccessible
      for i in [:indVal.nparams] do
        ctorArgs := ctorArgs.push (← `(_))
      for i in [:ctorInfo.nfields] do
        ctorArgs := ctorArgs.push (mkIdent (← mkFreshUserName `y))
      patterns := patterns.push (← `(@$(mkIdent ctorName):ident $ctorArgs:term*))
      let altRhs ← forallTelescopeReducing ctorInfo.type fun xs _ =>
        ctx.mkAltRhs ctx.toContextCore ctorName (Array.zip ctorArgs xs)
      let alt ← `(matchAltExpr| $[$patterns:term],* => $altRhs:term)
      alts := alts.push alt
    return alts

def mkAuxFunction (ctx : Context) (i : Nat) : TermElabM Syntax := do
  let auxFunName ← ctx.auxFunNames[i]
  let indVal     ← ctx.typeInfos[i]
  let header     ← mkHeader ctx indVal
  let mut body   ← mkMatch ctx header indVal header.argNames
  if ctx.usePartial then
    let letDecls ← mkLocalInstanceLetDecls ctx header.argNames
    body ← mkLet letDecls body
  let binders    := header.binders
  if ctx.usePartial then
    `(private partial def $(mkIdent auxFunName):ident $binders:explicitBinder* : $ctx.resultType:term := $body:term)
  else
    `(private def $(mkIdent auxFunName):ident $binders:explicitBinder* : $ctx.resultType:term := $body:term)

def mkMutualBlock (ctx : Context) : TermElabM Syntax := do
  let mut auxDefs := #[]
  for i in [:ctx.typeInfos.size] do
    auxDefs := auxDefs.push (← mkAuxFunction ctx i)
  `(mutual $auxDefs:command* end)

def mkInstanceCmds (ctx : Context) : TermElabM (Array Syntax) := do
  let mut instances := #[]
  for i in [:ctx.typeInfos.size] do
    let indVal       := ctx.typeInfos[i]
    let auxFunName   := ctx.auxFunNames[i]
    let argNames     ← mkInductArgNames indVal
    let binders      ← mkImplicitBinders argNames
    let binders      := binders ++ (← mkInstImplicitBinders ctx indVal argNames)
    let indType      ← mkInductiveApp indVal argNames
    let type         ← `($(mkIdent ctx.classInfo.name) $indType)
    let val          ← `(⟨$(mkIdent auxFunName)⟩)
    let instCmd ← `(instance $binders:implicitBinder* : $type := $val)
    trace[Meta.debug] "\n{instCmd}"
    instances := instances.push instCmd
  return instances

open Command

def mkDeriving (className : Name) (typeName : Name) (resultType : Syntax) (mkAltRhs : MkAltRhs) : CommandElabM Unit := do
  let cmds ← liftTermElabM none do
    let ctx ← mkContext className typeName resultType mkAltRhs
    let block ← mkMutualBlock ctx
    trace[Meta.debug] "\n{block}"
    return #[block] ++ (← mkInstanceCmds ctx)
  cmds.forM elabCommand

def mkDerivingToString (typeName : Name) : CommandElabM Unit := do
  mkDeriving `ToString typeName (← `(String)) fun ctx ctorName ctorArgs =>
    quote (toString ctorName) -- TODO

syntax[runTstKind] "runTst" : command

@[command_elab runTstKind] def elabTst : CommandElab := fun stx =>
  mkDerivingToString `Test.Foo

set_option trace.Meta.debug true
runTst
