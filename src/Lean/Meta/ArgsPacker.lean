/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude
import Lean.Meta.AppBuilder
import Lean.Meta.PProdN
import Lean.Meta.ArgsPacker.Basic

/-!
This module implements the equivalence between the types
```
(x : a) → (y : b) → r1[x,y],  (x : c) → (y : d) → r2[x,y]
```
(the “curried form”) and
```
(p : (a ⊗' b) ⊕' (c ⊗' d)) → r'[p]
```
where
```
r'[p] = match p with | inl (x,y) => r1[x,y] | inr (x,y) => r2[x,y]
```
(the “packed form”).

The `ArgsPacker` data structure (defined in `Lean.Meta.ArgsPacker.Basic` for fewer module
dependencies) contains necessary information to pack and unpack reliably. Care is taken that the
code is not confused even if the user intentionally uses a `PSigma` or `PSum` type, e.g. as the
ast parameter. Additionally, “good” variable names are stored here.

It is used in the translation of a possibly mutual, possibly n-ary recursive function to a single
unary function, which can then be made non-recursive using `WellFounded.fix`.  Additional users are
the `GuessLex` and `FunInd` modules, which also have to deal with this encoding.

Ideally, only this module has to know the precise encoding using `PSigma` and `PSigma`; all other
modules should only use the high-level functions at the bottom of this file. At the same time,
this module should be independent of WF-specific data structures (like `EqnInfos`).

The subnamespaces `Unary` and `Mutual` take care of `PSigma` resp. `PSum` packing, and are
intended to be local to this module.
-/

namespace Lean.Meta.ArgsPacker

open Lean Meta

namespace Unary

/-!
Helpers for iterated `PSigma`.
-/

/-
Given a telescope of FVars of type `tᵢ`, iterates `PSigma` to produce the type
`t₁ ⊗' t₂ …`.
-/
def packType (xs : Array Expr) : MetaM Expr := do
  if xs.isEmpty then
    return mkConst ``Unit
  let mut d ← inferType xs.back!
  for x in xs.pop.reverse do
    d ← mkAppOptM ``PSigma #[some (← inferType x), some (← mkLambdaFVars #[x] d)]
  return d


/--
Create a unary application by packing the given arguments using `PSigma.mk`.
The `type` should be the expected type of the packed argument, as created with `packType`.
-/
partial def pack (type : Expr) (args : Array Expr) : Expr :=
  if args.isEmpty then
    mkConst ``Unit.unit
  else
    go 0 type
where
  go (i : Nat) (type : Expr) : Expr :=
    if h : i < args.size - 1 then
      let arg := args[i]
      assert! type.isAppOfArity ``PSigma 2
      let us := type.getAppFn.constLevels!
      let α := type.appFn!.appArg!
      let β := type.appArg!
      assert! β.isLambda
      let type := β.bindingBody!.instantiate1 arg
      let rest := go (i+1) type
      mkApp4 (mkConst ``PSigma.mk us) α β arg rest
    else
      args[i]!

/--
Unpacks a unary packed argument created with `Unary.pack`.

Throws an error if the expression is not of that form.
-/
def unpack (arity : Nat) (e : Expr) : Option (Array Expr) := do
  if arity = 0 then return #[]
  let mut e := e
  let mut args := #[]
  while args.size + 1 < arity do
    if e.isAppOfArity ``PSigma.mk 4 then
      args := args.push (e.getArg! 2)
      e := e.getArg! 3
    else
      none
  args := args.push e
  return args

/--
  Given a (dependent) tuple `t` (using `PSigma`) of the given arity.
  Return an array containing its "elements".
  Example: `mkTupleElems a 4` returns `#[a.1, a.2.1, a.2.2.1, a.2.2.2]`.
  -/
private def mkTupleElems (t : Expr) (arity : Nat) : Array Expr := Id.run do
  if arity = 0 then return #[]
  let mut result := #[]
  let mut t := t
  for _ in [:arity - 1] do
    result := result.push (mkProj ``PSigma 0 t)
    t := mkProj ``PSigma 1 t
  result.push t

/--
Given a type `t` of the form `(x : A) → (y : B[x]) → … → (z : D[x,y]) → R[x,y,z]`
returns the curried type `(x : A ⊗' B ⊗' … ⊗' D) → R[x.1, x.2.1, x.2.2]`.
-/
def uncurryType (varNames : Array Name) (type : Expr) : MetaM Expr := do
  if varNames.isEmpty then
    mkArrow (mkConst ``Unit) type
  else
    forallBoundedTelescope type varNames.size fun xs _ => do
      assert! xs.size = varNames.size
      let d ← packType xs
      let name := if xs.size == 1 then varNames[0]! else `_x
      withLocalDeclD name d fun tuple => do
        let elems := mkTupleElems tuple xs.size
        let codomain ← instantiateForall type elems
        mkForallFVars #[tuple] codomain

/--
Iterated `PSigma.casesOn`:
Given `e : a ⊗' b ⊗' …` (where `e` is `FVarId`), a type `codomain[e]` of level `u`, and
`alt : (x : a) → (y : b) → … → codomain`, uses `PSigma.casesOn` to invoke `alt` on `e`.
-/
private def casesOn (varNames : List Name) (e : Expr) (u : Level) (codomain : Expr) (alt : Expr) : MetaM Expr := do
  match varNames with
  | [] => return alt
  | [_] => return alt.beta #[e]
  | n :: m :: ns => do
    let t ← inferType e
    match_expr t with
    | PSigma a b =>
      let us := t.getAppFn.constLevels!
      let motive ← mkLambdaFVars #[e] codomain
      let alt ←
        withLocalDeclD n a fun x => do
          withLocalDeclD m (b.beta #[x]) fun y => do
            let codomain' := motive.beta #[mkApp4 (.const ``PSigma.mk us) a b x y]
            mkLambdaFVars #[x,y] (← casesOn (m :: ns) y u codomain' (alt.beta #[x]))
      return mkApp5 (.const ``PSigma.casesOn (u :: us)) a b motive e alt
    | _ => throwError "ArgsPacker.Binary.casesOn: Expected PSigma type, got {t}"

/--
Given expression `e` of type `(x : A) → (y : B[x]) → … → (z : D[x,y]) → R[x,y,z]`
returns an expression of type `(x : A ⊗' B ⊗' … ⊗' D) → R[x.1, x.2.1, x.2.2]`.
-/
def uncurry (varNames : Array Name) (e : Expr) : MetaM Expr := do
  if varNames.isEmpty then
    return mkLambda `x .default (mkConst ``Unit) e
  else
    let type ← inferType e
    let resultType ← uncurryType varNames type
    forallBoundedTelescope resultType (some 1) fun xs codomain => do
      let #[x] := xs | unreachable!
      let u ← getLevel codomain
      let value ← casesOn varNames.toList x u codomain e
      mkLambdaFVars #[x] value

/-- Given `(A ⊗' B ⊗' … ⊗' D) → R` (non-dependent) `R`, return `A → B → … → D → R` -/
private def curryType (varNames : Array Name) (type : Expr) : MetaM Expr := do
  let some (domain, codomain) := type.arrow? |
    throwError "curryType: Expected arrow type, got {type}"
  go codomain varNames.toList domain
where
  go  (codomain : Expr) : List Name → Expr → MetaM Expr
  | [], _ => pure codomain
  | [_], domain => mkArrow domain codomain
  | n::ns, domain =>
    match_expr domain with
    | PSigma a b =>
      withLocalDecl n .default a fun x => do
        mkForallFVars #[x] (← go codomain ns (b.beta #[x]))
    | _ => throwError "curryType: Expected PSigma type, got {domain}"

/--
Given expression `e` of type `(x : A ⊗' B ⊗' … ⊗' D) → R[x]`
return expression of type `(x : A) → (y : B) → … → (z : D) → R[(x,y,z)]`
-/
private partial def curry (varNames : Array Name) (e : Expr) : MetaM Expr := do
  if varNames.isEmpty then
    return e.beta #[mkConst ``Unit.unit]
  let type ← whnfForall (← inferType e)
  unless type.isForall do
    throwError "curryPSigma: expected forall type, got {type}"
  let packedDomain := type.bindingDomain!
  go packedDomain packedDomain #[] varNames.toList
where
  go (packedDomain domain : Expr) args : List Name → MetaM Expr
  | [] => do
      let packedArg := Unary.pack packedDomain args
      return e.beta #[packedArg]
  | [n] => do
    withLocalDeclD n domain fun x => do
      let dummy := Expr.const ``Unit []
      mkLambdaFVars #[x] (← go packedDomain dummy (args.push x) [])
  | n :: ns =>
    match_expr domain with
    | PSigma a b =>
      withLocalDeclD n a fun x => do
        mkLambdaFVars #[x] (← go packedDomain (b.beta #[x]) (args.push x) ns)
    | _ => throwError "curryPSigma: Expected PSigma type, got {domain}"


end Unary

namespace Mutual

/-!
Helpers for iterated `PSum`.
-/

/-- Given types `#[t₁, t₂,…]`, returns the type `t₁ ⊕' t₂ …`. -/
def packType (ds : Array Expr) : MetaM Expr := do
  let mut r := ds.back!
  for d in ds.pop.reverse do
    r ← mkAppM ``PSum #[d, r]
  return r

/-- Given type `A ⊕' B ⊕' … ⊕' D`, return `[A, B, …, D]` -/
private def unpackType (n : Nat) (type : Expr) : MetaM (List Expr) :=
  match n with
  | 0 => pure []
  | 1 => pure [type]
  | n+1 =>
    match_expr type with
    | PSum a b => return a :: (← unpackType n b)
    | _ => throwError "Mutual.unpackType: Expected PSum type, got {type}"

/--
If `arg` is the argument to the `fidx`th of the `argsPacker.numFuncs` in the recursive group,
then `mk` packs that argument in `PSum.inl` and `PSum.inr` constructors
to create the mutual-packed argument of type `domain`.
-/
def pack (numFuncs : Nat) (domain : Expr) (fidx : Nat) (arg : Expr) : MetaM Expr := do
  let rec go (i : Nat) (type : Expr) : MetaM Expr := do
    if i >= numFuncs - 1 then
      return arg
    else
      (← whnfD type).withApp fun f args => do
        assert! args.size == 2
        if i == fidx then
          return mkApp3 (mkConst ``PSum.inl f.constLevels!) args[0]! args[1]! arg
        else
          let r ← go (i+1) args[1]!
          return mkApp3 (mkConst ``PSum.inr f.constLevels!) args[0]! args[1]! r
    termination_by numFuncs - 1 - i
  go 0 domain

/--
Unpacks a mutually packed argument created with `Mutual.mk` returning the
argument and function index.

Throws an error if the expression is not of that form.
-/
def unpack (numFuncs : Nat) (expr : Expr) : Option (Nat × Expr) := do
  let mut funidx := 0
  let mut e := expr
  while funidx + 1 < numFuncs do
    if e.isAppOfArity ``PSum.inr 3 then
      e := e.getArg! 2
      funidx := funidx + 1
    else if e.isAppOfArity ``PSum.inl 3 then
      e := e.getArg! 2
      break
    else
      none
  return (funidx, e)


/--
Given unary types `(x : Aᵢ) → Rᵢ[x]`, and `(x : A₁ ⊕ A₂ …)`, calculate the packed codomain
```
match x with | inl x₁ => R₁[x₁] | inr x₂ => R₂[x₂] | …
```
This function assumes (and does not check) that `Rᵢ` all have the same level.
-/
def mkCodomain (types : Array Expr) (x : Expr) : MetaM Expr := do
  let u ← forallBoundedTelescope types[0]! (some 1) fun _ body => getLevel body
  let rec go (x : Expr) (i : Nat) : MetaM Expr := do
    if i < types.size - 1 then
      let xType ← whnfD (← inferType x)
      assert! xType.isAppOfArity ``PSum 2
      let xTypeArgs := xType.getAppArgs
      let casesOn := mkConst ``PSum.casesOn (mkLevelSucc u :: xType.getAppFn.constLevels!)
      let casesOn := mkAppN casesOn xTypeArgs -- parameters
      let casesOn := mkApp casesOn (← mkLambdaFVars #[x] (mkSort u)) -- motive
      let casesOn := mkApp casesOn x -- major
      let minor1 ← withLocalDeclD (← mkFreshUserName `_x) xTypeArgs[0]! fun x => do
        mkLambdaFVars #[x] (types[i]!.bindingBody!.instantiate1 x)
      let minor2 ← withLocalDeclD (← mkFreshUserName `_x) xTypeArgs[1]! fun x => do
        mkLambdaFVars #[x] (← go x (i+1))
      return mkApp2 casesOn minor1 minor2
    else
      return types[i]!.bindingBody!.instantiate1 x
    termination_by types.size - 1 - i
  go x 0

/-
Given types `(x : A) → R₁[x]` and `(z : B) → R₂[z]`, returns the type
```
(x : A ⊕' B) → (match x with | .inl x => R₁[x] | .inr R₂[z]
```
if the codomains are dependent, or
```
(x : A ⊕' B) → R
```
if they are all the same.

-/
def uncurryType (types : Array Expr) : MetaM Expr := do
  if types.size = 1 then
    return types[0]!
  let types ← types.mapM whnfForall
  types.forM fun type => do
    unless type.isForall do
      throwError "Mutual.uncurryType: Expected forall type, got {type}"
  let domain ← packType (types.map (·.bindingDomain!))
  withLocalDeclD (← mkFreshUserName `x) domain fun x => do
    let codomain ← Mutual.mkCodomain types x
    mkForallFVars #[x] codomain

/-
Given types `(x : A) → R` and `(z : B) → R`, returns the type
```
(x : A ⊕' B) → R
```
-/
def uncurryTypeND (types : Array Expr) : MetaM Expr := do
  let types ← types.mapM whnfForall
  types.forM fun type =>
    unless type.isArrow do
      throwError "Mutual.uncurryTypeND: Expected non-dependent types, got {type}"
  let codomains := types.map (·.bindingBody!)
  let t' := codomains.back!
  codomains.pop.forM fun t =>
    unless ← isDefEq t t' do
      throwError "Mutual.uncurryTypeND: Expected equal codomains, but got {t} and {t'}"
  let codomain := codomains[0]!
  let domain ← packType (types.map (·.bindingDomain!))
  mkArrow domain codomain

/-
Iterated `PSum.casesOn`:
Given a value `(x : A ⊕ C)` (which must be a FVar) and functions
`alt₁ : (a : A) → codomain[inl a]` and `alt₂ : (b : B) → codomain[inr b]`,
matches on `x` to apply the right `alt` to produce a value of `codomain[x]`.

Uses the variable name from the lambda in `altᵢ`, if present.
-/
private def casesOn (x : Expr) (codomain : Expr) (alts : List Expr) : MetaM Expr := do
  match alts with
  | [] => throwError "Mutual.casesOn: no alternatives"
  | [alt] => return alt.beta #[x]
  | alt₁ :: alts => do
    let t ← inferType x
    match_expr t with
    | PSum a b =>
      let u ← getLevel codomain
      let us := t.getAppFn.constLevels!
      let motive ← mkLambdaFVars #[x] codomain
      let alt₂ ←
        if let [alt] := alts then pure alt else
        withLocalDeclD (← mkFreshUserName `_x) b fun y => do
          let codomain' := motive.beta #[mkApp3 (.const ``PSum.inr us) a b y]
          mkLambdaFVars #[y] (← casesOn y codomain' alts)
      return mkApp6 (.const ``PSum.casesOn (u::us)) a b motive x alt₁ alt₂
    | _ => throwError "Mutual.casesOn: Expected PSum type, got {t}"

/--
Given unary expressions `e₁`, `e₂` with types `(x : A) → R₁[x]`
and `(z : C) → R₂[z]`, returns an expression of type
```
(x : A ⊕' C) → (match x with | .inl x => R₁[x] | .inr R₂[z])
```
-/
def uncurryWithType (resultType : Expr) (es : Array Expr) : MetaM Expr := do
  forallBoundedTelescope resultType (some 1) fun xs codomain => do
    let #[x] := xs | unreachable!
    let value ← casesOn x codomain es.toList
    mkLambdaFVars #[x] value

def uncurry (es : Array Expr) : MetaM Expr := do
  let types ← es.mapM inferType
  let resultType ← uncurryType types
  uncurryWithType resultType es

/--
Given unary expressions `e₁`, `e₂` with types `(x : A) → R`
and `(z : C) → R`, returns an expression of type
```
(x : A ⊕' C) → R
```
-/
def uncurryND (es : Array Expr) : MetaM Expr := do
  let types ← es.mapM inferType
  let resultType ← uncurryTypeND types
  forallBoundedTelescope resultType (some 1) fun xs codomain => do
    let #[x] := xs | unreachable!
    let value ← casesOn x codomain es.toList
    mkLambdaFVars #[x] value

/-
Given type `(A ⊕' C) → R` (non-depenent), return types
```
#[A → R, B → R]
```
-/
def curryType (n : Nat) (type : Expr) : MetaM (Array Expr) := do
  let some (domain, codomain) := type.arrow? |
    throwError "curryType: Expected arrow type, got {type}"
  let ds ← unpackType n domain
  ds.toArray.mapM (fun d => mkArrow d codomain)

end Mutual

-- Now for the main definitions in this module

/-- The number of functions being packed -/
def numFuncs (argsPacker : ArgsPacker) : Nat := argsPacker.varNamess.size

/-- The arities of the functions being packed -/
def arities (argsPacker : ArgsPacker) : Array Nat := argsPacker.varNamess.map (·.size)

def onlyOneUnary (argsPacker : ArgsPacker) :=
  argsPacker.varNamess.size = 1 &&
  argsPacker.varNamess[0]!.size = 1

def pack (argsPacker : ArgsPacker) (domain : Expr) (fidx : Nat) (args : Array Expr)
    : MetaM Expr := do
  assert! fidx < argsPacker.numFuncs
  assert! args.size == argsPacker.varNamess[fidx]!.size
  let types ← Mutual.unpackType argsPacker.numFuncs domain
  let type := types[fidx]!
  Mutual.pack argsPacker.numFuncs domain fidx (Unary.pack type args)

/--
Given the packed argument of a (possibly) mutual and (possibly) nary call,
return the function index that is called and the arguments individually.

We expect precisely the expressions produced by `pack`, with manifest
`PSum.inr`, `PSum.inl` and `PSigma.mk` constructors, and thus take them apart
rather than using projections.
-/
def unpack (argsPacker : ArgsPacker) (e : Expr) : Option (Nat × Array Expr) := do
  let (funidx, e) ← Mutual.unpack argsPacker.numFuncs e
  let args ← Unary.unpack argsPacker.varNamess[funidx]!.size e
  return (funidx, args)

/--
Given types `(x : A) → (y : B[x]) → R₁[x,y]` and `(z : C) → R₂[z]`, returns the type uncurried type
```
(x : (A ⊗ B) ⊕ C) → (match x with | .inl (x, y) => R₁[x,y] | .inr R₂[z]
```
-/
def uncurryType (argsPacker : ArgsPacker) (types : Array Expr) : MetaM Expr := do
  let unary ← (Array.zipWith Unary.uncurryType argsPacker.varNamess types).mapM id
  Mutual.uncurryType unary

/--
Given expressions `e₁`, `e₂` with types `(x : A) → (y : B[x]) → R₁[x,y]`
and `(z : C) → R₂[z]`, returns an expression of type
```
(x : (A ⊗ B) ⊕ C) → (match x with | .inl (x, y) => R₁[x,y] | .inr R₂[z]
```
-/
def uncurry (argsPacker : ArgsPacker) (es : Array Expr) : MetaM Expr := do
  let unary ← (Array.zipWith Unary.uncurry argsPacker.varNamess es).mapM id
  Mutual.uncurry unary

def uncurryWithType (argsPacker : ArgsPacker) (resultType : Expr) (es : Array Expr) : MetaM Expr := do
  let unary ← (Array.zipWith Unary.uncurry argsPacker.varNamess es).mapM id
  Mutual.uncurryWithType resultType unary

/--
Given expressions `e₁`, `e₂` with types `(x : A) → (y : B[x]) → R`
and `(z : C) → R`, returns an expression of type
```
(x : (A ⊗ B) ⊕ C) → R
```
-/
def uncurryND (argsPacker : ArgsPacker) (es : Array Expr) : MetaM Expr := do
  let unary ← (Array.zipWith Unary.uncurry argsPacker.varNamess es).mapM id
  Mutual.uncurryND unary

/--
Given expression `e` of type `(x : a₁ ⊗' b₁ ⊕' a₂ ⊗' d₂ …) → e[x]`, uncurries the expression and
projects to the `i`th function of type,
```
((x : aᵢ) → (y : bᵢ) → e[.inr….inl (x,y)])
```
-/
def curryProj (argsPacker : ArgsPacker) (e : Expr) (i : Nat) : MetaM Expr := do
  let n := argsPacker.numFuncs
  let t ← whnf (← inferType e)
  unless t.isForall do
    panic! "curryProj: expected forall type, got {}"
  let packedDomain := t.bindingDomain!
  let unaryTypes ← Mutual.unpackType n packedDomain
  unless i < unaryTypes.length do
    throwError "curryProj: index out of range"
  let unaryType := unaryTypes[i]!
  -- unary : (x : a ⊗ b) → e[inl x]
  let unary ← withLocalDeclD t.bindingName! unaryType fun x => do
      let packedArg ← Mutual.pack unaryTypes.length packedDomain i x
      mkLambdaFVars #[x] (e.beta #[packedArg])
  -- nary : (x : a) → (y : b) → e[inl (x,y)]
  Unary.curry argsPacker.varNamess[i]! unary


/--
Given type `(x : a ⊗' b ⊕' c ⊗' d) → R` (non-dependent), return types
```
#[(x: a) → (y : b) → R, (x : c) → (y : d) → R]
```
-/
def curryType (argsPacker : ArgsPacker) (t : Expr) : MetaM (Array Expr) := do
  let unary ← Mutual.curryType argsPacker.numFuncs t
  (Array.zipWith Unary.curryType argsPacker.varNamess unary).mapM id

/--
Given expression `e` of type `(x : a ⊗' b ⊕' c ⊗' d) → e[x]`, wraps that expression
to produce an expression of the isomorphic type
```
((x: a) → (y : b) → e[.inl (x,y)]) ∧ ((x : c) → (y : d) → e[.inr (x,y)])
```
-/
def curry (argsPacker : ArgsPacker) (e : Expr) : MetaM Expr := do
  let mut es := #[]
  for i in [:argsPacker.numFuncs] do
    es := es.push (← argsPacker.curryProj e i)
  PProdN.mk 0 es

/--
Given type `(a ⊗' b ⊕' c ⊗' d) → e`, brings `a → b → e` and `c → d → e`
into scope as fresh local declarations and passes their FVars to the continuation `k`.
The `name` is used to form the variable names; uses `name1`, `name2`, … if there are multiple.
-/
private def withCurriedDecl {α} (argsPacker : ArgsPacker) (name : Name) (type : Expr)
    (k : Array Expr → MetaM α) : MetaM α := do
  go (← argsPacker.curryType type).toList #[]
where
  go : List Expr → Array Expr → MetaM α
  | [], acc => k acc
  | t::ts, acc => do
    let name := if argsPacker.numFuncs = 1 then name else .mkSimple s!"{name}{acc.size + 1}"
    withLocalDeclD name t fun x => do
      go ts (acc.push x)

/--
Given `value : type` where `type` is
```
(m : a ⊗' b ⊕' c ⊗' d → s) → r[m]
```
brings `m1 : a → b → s` and `m2 : c → d → s` into scope. The continuation receives

 * FVars for `m1`…
 * `e[m]`
 * `t[m]`

where `m : a ⊗' b ⊕' c ⊗' d → s` is the uncurried form of `m1` and `m2`.

The variable names `m1` and `m2` are taken from the parameter name in `t`, with numbers added
unless `numFuns = 1`
-/
def curryParam {α} (argsPacker : ArgsPacker) (value : Expr) (type : Expr)
    (k : Array Expr → Expr → Expr → MetaM α) : MetaM α := do
  unless type.isForall do
    throwError "uncurryParam: expected forall, got {type}"
  let packedMotiveType := type.bindingDomain!
  unless packedMotiveType.isArrow do
    throwError "uncurryParam: unexpected packed motive {packedMotiveType}"
  -- Bring unpacked motives (motive1 : a → b → Prop and motive2 : c → d → Prop) into scope
  withCurriedDecl argsPacker type.bindingName! packedMotiveType fun motives => do
    -- Combine them into a packed motive (motive : a ⊗' b ⊕' c ⊗' d → Prop), and use that
    let motive ← argsPacker.uncurryND motives
    let type ← instantiateForall type #[motive]
    let value := mkApp value motive
    k motives value type



end Lean.Meta.ArgsPacker
