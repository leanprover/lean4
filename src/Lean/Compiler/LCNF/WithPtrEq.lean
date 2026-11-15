/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Lean.Meta.Basic
import Lean.Meta.InferType
import Lean.Meta.WHNF

/-!
# Type check for `withPtrEq`

`withPtrEq a b k h` is logically equal to `k ()`, but the compiler implements it by
`withPtrEqUnsafe`, which returns `true` without calling `k` if `a` and `b` are pointer-equal. This
is only correct if pointer equality implies equality for values of the type of `a` and `b`.

The compiler erases proofs as well as values whose type is a sort or a type former. Erasing proofs
is harmless because of proof irrelevance, but two values that differ only in an erased type may be
represented by the same object at runtime. `checkWithPtrEqType` therefore checks conservatively that
values of the given type cannot contain types or type formers:

* proofs are accepted;
* sorts and type formers are rejected;
* a function type is accepted if its codomain is accepted: then a closure determines the result
  for each argument, and hence the function by function extensionality;
* an inductive type is accepted if the types of all constructor fields are accepted, where
  occurrences of an inductive type that is already being checked are accepted (this is sound by
  induction on values);
* a quotient is accepted if the underlying type is accepted;
* everything else, in particular type variables, opaque types and types whose definition is not
  accessible in the current module, is rejected.
-/

namespace Lean.Compiler.LCNF

namespace WithPtrEq

structure Context where
  /-- The type at which `withPtrEq` is used. -/
  rootType : Expr
  /-- The constructor and the name of the field whose type is currently being checked. -/
  field? : Option (Name × Name) := none

/--
The state contains the inductive types, applied to their parameters, that are currently being
checked or have already been accepted.
-/
abbrev M := ReaderT Context <| StateRefT (Std.HashSet Expr) MetaM

def throwUnsupported (type : Expr) (reason : MessageData) : M α := do
  let ctx ← read
  let subject := if ctx.field?.isNone && type == ctx.rootType then
      m!"values of this type"
    else
      m!"it contains values of type{indentExpr type}\nwhich"
  let loc := match ctx.field? with
    | some (ctorName, fieldName) =>
      m!" (in field `{fieldName}` of constructor `{.ofConstName ctorName}`)"
    | none => m!""
  let withPtrEq := MessageData.ofConstName ``withPtrEq
  throwError (m!"failed to compile definition, `{withPtrEq}` cannot be used at type\
    {indentExpr ctx.rootType}\nbecause {subject} {reason}{loc}." ++
    .note m!"`{withPtrEq}` is implemented by a pointer equality check, which is only correct if \
      pointer-equal values are equal. This is not the case for values that contain types or type \
      formers, since these are erased at runtime. Therefore, `{withPtrEq}` can only be used at \
      types for which the compiler can check that their values do not contain types or type \
      formers; in particular, it cannot be used polymorphically." ++
    .hint' m!"In `unsafe` code, `{.ofConstName ``withPtrEqUnsafe}` can be used instead.")

partial def check (type : Expr) : M Unit := withIncRecDepth do
  if ← Meta.isProp type then
    return
  -- Deliberately not `Meta.isTypeFormerType`, which reduces with default transparency: values of an
  -- `@[irreducible]` alias of `Prop` are still erased wherever they are created at type `Prop`.
  let typeWhnf ← Meta.whnf type
  match typeWhnf with
  | .sort .. => throwUnsupported type m!"are erased at runtime"
  | .forallE .. =>
    Meta.forallTelescopeReducing typeWhnf (whnfType := true) fun _ codomain => do
      if codomain.isSort then
        throwUnsupported type m!"are erased at runtime"
      check codomain
  | _ =>
    let fn := typeWhnf.getAppFn
    let args := typeWhnf.getAppArgs
    match fn with
    | .fvar .. =>
      throwUnsupported type m!"cannot be checked since `{fn}` is a type variable"
    | .const declName us =>
      match (← getEnv).find? declName with
      | some (.inductInfo val) => checkInductive type val us args
      | some (.quotInfo _) =>
        if declName == ``Quot && args.size == 2 then
          check args[0]!
        else
          throwStuck type
      | _ => throwStuck type
    | _ => throwStuck type
where
  throwStuck (type : Expr) : M Unit :=
    throwUnsupported type m!"cannot be checked since the type does not reduce to an inductive \
      type, a function type or a quotient"

  checkInductive (type : Expr) (val : InductiveVal) (us : List Level) (args : Array Expr) :
      M Unit := do
    unless args.size == val.numParams + val.numIndices do
      throwStuck type
    let params := args[*...val.numParams].toArray
    let key := mkAppN (.const val.name us) params
    if (← get).contains key then
      return
    modify (·.insert key)
    for ctorName in val.ctors do
      let some (.ctorInfo ctorVal) := (← getEnv).find? ctorName
        | throwUnsupported type m!"cannot be checked since the constructor \
            `{.ofConstName ctorName}` is not accessible"
      let ctorType ← Meta.instantiateForall
        (ctorVal.type.instantiateLevelParams ctorVal.levelParams us) params
      Meta.forallBoundedTelescope ctorType ctorVal.numFields fun fields _ => do
        for field in fields do
          let fieldName ← field.fvarId!.getUserName
          withReader ({ · with field? := some (ctorName, fieldName) }) do
            check (← Meta.inferType field)

end WithPtrEq

/--
Checks that pointer equality implies equality for values of `type`, which is required for
compiling `withPtrEq` at `type`, and throws an error otherwise. See the module docstring for
details.
-/
public def checkWithPtrEqType (type : Expr) : MetaM Unit :=
  Meta.withTransparency .all do
    WithPtrEq.check type |>.run { rootType := type } |>.run' {}

end Lean.Compiler.LCNF
