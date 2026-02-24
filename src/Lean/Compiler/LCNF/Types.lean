/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.BorrowedAnnotation
public import Lean.Meta.InferType
import Init.Omega
import Lean.OriginalConstKind

public section

namespace Lean.Compiler

scoped notation:max "◾" => lcErased

namespace LCNF

def erasedExpr := mkConst ``lcErased
def anyExpr := mkConst ``lcAny

def _root_.Lean.Expr.isVoid (e : Expr) :=
  e.isAppOf ``lcVoid

def _root_.Lean.Expr.isErased (e : Expr) :=
  e.isAppOf ``lcErased

def _root_.Lean.Expr.isAny (e : Expr) :=
  e.isAppOf ``lcAny

def isPropFormerTypeQuick : Expr → Bool
  | .forallE _ _ b _ => isPropFormerTypeQuick b
  | .sort .zero => true
  | _ => false

/--
Return true iff `type` is `Prop` or `As → Prop`.
-/
partial def isPropFormerType (type : Expr) : MetaM Bool := do
  match isPropFormerTypeQuick type with
  | true => return true
  | false => go type #[]
where
  go (type : Expr) (xs : Array Expr) : MetaM Bool := do
    match type with
    | .sort .zero => return true
    | .forallE n d b c => Meta.withLocalDecl n c (d.instantiateRev xs) fun x => go b (xs.push x)
    | _ =>
      let type ← Meta.whnfD (type.instantiateRev xs)
      match type with
      | .sort .zero => return true
      | .forallE .. => go type #[]
      | _ => return false

/--
Return true iff `e : Prop` or `e : As → Prop`.
-/
def isPropFormer (e : Expr) : MetaM Bool := do
  isPropFormerType (← Meta.inferType e)

/-!
The code generator uses a format based on A-normal form.
This normal form uses many let-expressions and it is very convenient for
applying compiler transformations. However, it creates a few issues
in a dependently typed programming language.

- Many casts are needed.
- It is too expensive to ensure we are not losing typeability when creating join points
  and simplifying let-values
- It may not be possible to create a join point because the resulting expression is
  not type correct. For example, suppose we are trying to create a join point for
  making the following `match` terminal.
  ```
  let x := match a with | true => b | false => c;
  k[x]
  ```
  and want to transform this code into
  ```
  let jp := fun x => k[x]
  match a with
  | true => jp b
  | false => jp c
  ```
  where `jp` is a new join point (i.e., a local function that is always fully applied and
  tail recursive). In many examples in the Lean code-base, we have to skip this transformation
  because it produces a type-incorrect term. Recall that types/propositions in `k[x]` may rely on
  the fact that `x` is definitionally equal to `match a with ...` before the creation of
  the join point.

Thus, in the first code generator pass, we convert types into a `LCNFType` (Lean Compiler Normal Form Type).
The method `toLCNFType` produces a type with the following properties:

- All constants occurring in the result type are inductive datatypes.
- The arguments of type formers are type formers, or `◾`. We use `◾` to denote erased information.
- All type definitions are expanded. If reduction gets stuck, it is replaced with `◾`.

Remark: you can view `◾` occurring in a type position as the "any type".
Remark: in our runtime, `◾` is represented as `box(0)`.

The goal is to preserve as much information as possible and avoid the problems described above.
Then, we don't have `let x := v; ...` in LCNF code when `x` is a type former.
If the user provides a `let x := v; ...` where x is a type former, we can always expand it when
converting into LCNF.
Thus, given a `let x := v, ...` in occurring in LCNF, we know `x` cannot occur in any type since it is
not a type former.

We try to preserve type information because they unlock new optimizations, and we can type check
the result produced by each code generator step.


Below, we provide some example programs and their erased variants:
-- 1. Source type: `f: (n: Nat) -> (tupleN Nat n)`.
      LCNF type: `f: Nat -> ◾`.
      We convert the return type `(tupleN Nat n) to `◾`, since we cannot reduce
      `(tupleN Nat n)` to a term of the form `(InductiveTy ...)`.

-- 2. Source type: `f: (n: Nat) (fin: Fin n) -> (tupleN Nat fin)`.
      LCNF type: `f: Nat -> Fin ◾ -> ◾`.
      Since `(Fin n)` has dependency on `n`, we erase the `n` to get the
      type `(Fin ◾)`.
-/

open Meta in
/--
Convert a Lean type into a LCNF type used by the code generator.
-/
partial def toLCNFType (type : Expr) : MetaM Expr := do
  let res ← go type
  if (← getEnv).header.isModule then
    -- Under the module system, `type` may reduce differently in different modules, leading to
    -- IR-level mismatches and thus undefined behavior. We want to make this part independent of the
    -- current module and its view of the environment but until then, we force the user to make
    -- involved type definitions exposed by checking whether we would infer a different type in the
    -- public scope. We ignore failed inference in the public scope because it can easily fail when
    -- compiling private declarations using private types, and even if that private code should
    -- escape into different modules, it can only generate a static error there, not a
    -- miscompilation.
    -- Note that always using `withExporting` would not always be correct either because it is
    -- ignored in non-`module`s and thus mismatches with upstream `module`s may again occur.
    let res'? ← observing <| withExporting <| go type
    if let .ok res' := res'? then
      if res != res' then
        let mut reason := m!"locally inferred compilation type{indentD res}\n\
          differs from type{indentD res'}\n\
          that would be inferred in other modules. This usually means that a type `def` involved \
          with the mentioned declarations needs to be `@[expose]`d. "
        -- The above error message is terrible to read, so we'll try to condense it to the essential
        -- list of non-exposed definitions.
        let origDiag := (← get).diag
        try
          let _ ← observing <| withOptions (diagnostics.set · true)  <| withExporting <| go type
          let env ← getEnv
          let blocked := (← get).diag.unfoldAxiomCounter.toList.filterMap fun (n, count) => do
            let count := count - origDiag.unfoldAxiomCounter.findD n 0
            guard <| count > 0 && getOriginalConstKind? env n matches some .defn
            return m!"{.ofConstName n} ↦ {count}"
          if !blocked.isEmpty then
            reason := m!"locally inferred compilation type differs from type that would be \
              inferred in other modules. Some of the following definitions may need to be \
              `@[expose]`d to fix this mismatch: {indentD <| .joinSep blocked Format.line}\n"
        finally
          modify ({ · with diag := origDiag })
        throwError "Compilation failed, {reason}This is a current compiler \
          limitation for `module`s that may be lifted in the future."
  return res
where
  go type := do
    if ← isProp type then
      return erasedExpr
    let type ← whnfEta type
    match type with
    | .sort u     => return .sort u
    | .const ..   => visitApp type #[]
    | .lam n d b bi =>
      withLocalDecl n bi d fun x => do
        let d ← go d
        let b ← go (b.instantiate1 x)
        if b.isErased then
          return b
        else
          return Expr.lam n d (b.abstract #[x]) bi
    | .forallE .. => visitForall type #[]
    | .app ..  => type.withApp visitApp
    | .fvar .. => visitApp type #[]
    | .proj ``Subtype 0 (.app (.const ``Void.nonemptyType []) _) =>
      return mkConst ``lcVoid
    | _        => return mkConst ``lcAny

  whnfEta (type : Expr) : MetaM Expr := do
    -- We increase transparency here to unfold type aliases of functions that are declared as
    -- `irreducible`, such that they end up being represented as C functions.
    let type ← withTransparency .all do
      whnf type
    let type' := type.eta
    if type' != type then
      whnfEta type'
    else
      return type

  visitForall (e : Expr) (xs : Array Expr) : MetaM Expr := do
    match e with
    | .forallE n d b bi =>
      let d := d.instantiateRev xs
      withLocalDecl n bi d fun x => do
        let isBorrowed := isMarkedBorrowed d
        let mut d := (← go d).abstract xs
        if isBorrowed then
          d := markBorrowed d
        return .forallE n d (← visitForall b (xs.push x)) bi
    | _ =>
      let e ← go (e.instantiateRev xs)
      return e.abstract xs

  visitApp (f : Expr) (args : Array Expr) := do
    let fNew ← match f with
      | .const declName us =>
        if (← getEnv).isExporting && isPrivateName declName then
          -- This branch can happen under `backward.privateInPublic`; restore original behavior of
          -- failing here, which is caught and ignored above by `observing`.
          throwError "internal compiler error: private in public"
        if declName == ``Quot then
          return (← go args[0]!)
        let .inductInfo _ ← getConstInfo declName | return anyExpr
        pure <| .const declName us
      | .fvar .. => pure f
      | _ => return anyExpr
    let mut result := fNew
    for arg in args do
      if ← isProp arg <||> isPropFormer arg then
        result := mkApp result erasedExpr
      else if ← isTypeFormer arg then
        result := mkApp result (← go arg)
      else
        result := mkApp result (mkConst ``lcAny)
    return result

mutual

partial def joinTypes (a b : Expr) : Expr :=
  joinTypes? a b |>.getD (mkConst ``lcAny)

partial def joinTypes? (a b : Expr) : Option Expr := do
  if a.isErased || b.isErased then
    return erasedExpr -- See comment at `compatibleTypes`.
  else if a == b then
    return a
  else
    let a' := a.headBeta
    let b' := b.headBeta
    if a != a' || b != b' then
      joinTypes? a' b'
    else
      match a, b with
      | .mdata _ a, b => joinTypes? a b
      | a, .mdata _ b => joinTypes? a b
      | .app f a, .app g b =>
        (do return .app (← joinTypes? f g) (← joinTypes? a b))
         <|>
        return (mkConst ``lcAny)
      | .forallE n d₁ b₁ _, .forallE _ d₂ b₂ _ =>
        (do return .forallE n (← joinTypes? d₁ d₂) (joinTypes b₁ b₂) .default)
        <|>
        return (mkConst ``lcAny)
      | .lam n d₁ b₁ _, .lam _ d₂ b₂ _ =>
        (do return .lam n (← joinTypes? d₁ d₂) (joinTypes b₁ b₂) .default)
        <|>
        return (mkConst ``lcAny)
      | _, _ => return (mkConst ``lcAny)

end

/--
Return `true` if `type` is a LCNF type former type.

Remark: This is faster than `Lean.Meta.isTypeFormer`, as this
        assumes that the input `type` is an LCNF type.
-/
partial def isTypeFormerType (type : Expr) : Bool :=
  match type.headBeta with
  | .sort .. => true
  | .forallE _ _ b _ => isTypeFormerType b
  | _ => false

/--
Given a LCNF `type` of the form `forall (a_1 : A_1) ... (a_n : A_n), B[a_1, ..., a_n]` and `p_1 : A_1, ... p_n : A_n`,
return `B[p_1, ..., p_n]`.

Remark: similar to `Meta.instantiateForall`, buf for LCNF types.
-/
def instantiateForall (type : Expr) (ps : Array Expr) : CoreM Expr :=
  go 0 type
where
  go (i : Nat) (type : Expr) : CoreM Expr :=
    if h : i < ps.size then
      if let .forallE _ _ b _ := type.headBeta then
        go (i+1) (b.instantiate1 ps[i])
      else
        throwError "invalid instantiateForall, too many parameters"
    else
      return type
  termination_by ps.size - i

/--
Return `true` if `type` is a predicate.
Examples: `Nat → Prop`, `Prop`, `Int → Bool → Prop`.
-/
partial def isPredicateType (type : Expr) : Bool :=
  match type.headBeta with
  | .sort .zero => true
  | .forallE _ _ b _ => isPredicateType b
  | _ => false

/--
Return `true` if `type` is a LCNF type former type or it is an "any" type.
This function is similar to `isTypeFormerType`, but more liberal.
For example, `isTypeFormerType` returns false for `◾` and `Nat → ◾`, but
this function returns true.
-/
partial def maybeTypeFormerType (type : Expr) : Bool :=
  match type.headBeta with
  | .sort .. => true
  | .forallE _ _ b _ => maybeTypeFormerType b
  | _ => type.isErased

/--
`isClass? type` return `some ClsName` if the LCNF `type` is an instance of the class `ClsName`.
-/
def isClass? (type : Expr) : CoreM (Option Name) := do
  let .const declName _ := type.getAppFn | return none
  if isClass (← getEnv) declName then
    return declName
  else
    return none

/--
`isArrowClass? type` return `some ClsName` if the LCNF `type` is an instance of the class `ClsName`, or
if it is arrow producing an instance of the class `ClsName`.
-/
partial def isArrowClass? (type : Expr) : CoreM (Option Name) := do
  match type.headBeta with
  | .forallE _ _ b _ => isArrowClass? b
  | _ => isClass? type

partial def getArrowArity (e : Expr) :=
  match e.headBeta with
  | .forallE _ _ b _ => getArrowArity b + 1
  | _ => 0

/-- Return `true` if `type` is an inductive datatype with 0 constructors. -/
def isInductiveWithNoCtors (type : Expr) : CoreM Bool := do
  let .const declName _ := type.getAppFn | return false
  let some (.inductInfo info) := (← getEnv).find? declName | return false
  return info.numCtors == 0

def mkBoxedName (n : Name) : Name :=
  Name.mkStr n "_boxed"

def isBoxedName (name : Name) : Bool :=
  name matches .str _ "_boxed"

namespace ImpureType

/-!
This section defines the low level IR types used in the impure phase of LCNF.
-/

/--
`float` is a 64-bit floating point number.
-/
@[inline, expose, match_pattern]
def float : Expr := .const ``Float []


/--
`float32` is a 32-bit floating point number.
-/
@[inline, expose, match_pattern]
def float32 : Expr := .const ``Float32 []

/--
`uint8` is an 8-bit unsigned integer.
-/
@[inline, expose, match_pattern]
def uint8 : Expr := .const ``UInt8 []

/--
`uint16` is a 16-bit unsigned integer.
-/
@[inline, expose, match_pattern]
def uint16 : Expr := .const ``UInt16 []

/--
`uint32` is a 32-bit unsigned integer.
-/
@[inline, expose, match_pattern]
def uint32 : Expr := .const ``UInt32 []

/--
`uint64` is a 64-bit unsigned integer.
-/
@[inline, expose, match_pattern]
def uint64 : Expr := .const ``UInt64 []

/--
`usize` represents the C `size_t` type. It has a separate representation because depending on the
target architecture it has a different width and we try to generate platform independent C code.

We generally assume that `sizeof(size_t) == sizeof(void)`.
-/
@[inline, expose, match_pattern]
def usize : Expr := .const ``USize []

/--
`erased` represents type arguments, propositions and proofs which are no longer relevant at this
point in time.
-/
@[inline, expose, match_pattern]
def erased : Expr := .const ``lcErased []

/-
`object` is a pointer to a value in the heap.
-/
@[inline, expose, match_pattern]
def object : Expr := .const `obj []

/--
`tobject` is either an `object` or a `tagged` pointer.

Crucially the RC the RC operations for `tobject` are slightly more expensive because we
first need to test whether the `tobject` is really a pointer or not.
-/
@[inline, expose, match_pattern]
def tobject : Expr := .const `tobj []

/--
tagged` is a tagged pointer (i.e., the least significant bit is 1) storing a scalar value.
-/
@[inline, expose, match_pattern]
def tagged : Expr := .const `tagged []

/--
`void` is used to identify uses of the state token from `BaseIO` which do no longer need
to be passed around etc. at this point in the pipeline.
-/
@[inline, expose, match_pattern]
def void : Expr := .const ``lcVoid []

/--
Whether the type is a scalar as opposed to a pointer (or a value disguised as a pointer).
-/
def Lean.Expr.isScalar : Expr → Bool
  | ImpureType.float    => true
  | ImpureType.float32  => true
  | ImpureType.uint8    => true
  | ImpureType.uint16   => true
  | ImpureType.uint32   => true
  | ImpureType.uint64   => true
  | ImpureType.usize    => true
  | _        => false

/--
Whether the type is an object which is to say a pointer or a value disguised as a pointer.
-/
def Lean.Expr.isObj : Expr → Bool
  | ImpureType.object  => true
  | ImpureType.tagged  => true
  | ImpureType.tobject => true
  | ImpureType.void    => true
  | _       => false

/--
Whether the type might be an actual pointer (crucially this excludes `tagged`).
-/
def Lean.Expr.isPossibleRef : Expr → Bool
  | ImpureType.object | ImpureType.tobject => true
  | _ => false

/--
Whether the type is a pointer for sure.
-/
def Lean.Expr.isDefiniteRef : Expr → Bool
  | ImpureType.object => true
  | _ => false

/--
The boxed version of types.
-/
def Lean.Expr.boxed : Expr → Expr
  | ImpureType.object | ImpureType.float | ImpureType.float32 | ImpureType.uint64 =>
    ImpureType.object
  | ImpureType.void | ImpureType.tagged | ImpureType.uint8 | ImpureType.uint16 => ImpureType.tagged
  | _ => ImpureType.tobject

end ImpureType

end Lean.Compiler.LCNF
