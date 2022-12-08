/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.InferType

namespace Lean.Compiler.LCNF

/-!
# Compatible Types

We used to type check LCNF after each compiler pass. However, we disable this capability because cast management was too costly.
The casts may be needed to ensure the result of each pass is still typeable.
However, these sanity checks are useful for catching silly mistakes.
Thus, we have added an "LCNF type linter". When turned on, this "linter" option instructs the compiler to perform compatibility type checking
in the LCNF code after some compiler passes.
Recall most casts are only needed in functions that make heavy use of dependent types.
We claim it is "defensible" to say this sanity checker is a linter. If the sanity checker fails, it means the user is "abusing" dependent types
and performance may suffer at runtime.
Here is an example of code that "abuses" dependent types:
```
def Tuple (α : Type u) : Nat → Type u
  | 0   => PUnit
  | 1   => α
  | n+2 => α × Tuple α (n+1)

def mkConstTuple (a : α) : (n : Nat) → Tuple α n
  | 0 => ⟨⟩
  | 1 => a
  | n+2 => (a, mkConstTuple a (n+1))

def Tuple.map (f : α → β) (xs : Tuple α n) : Tuple β n :=
  match n with
  | 0 => ⟨⟩
  | 1 => f xs
  | _+2 => match xs with
    | (a, xs) => (f a, Tuple.map f xs)
```
-/


/--
Quick check for `compatibleTypes`. It is not monadic, but it is incomplete
because it does not eta-expand type formers. See comment at `compatibleTypes`.
Remark: if the result is `true`, then `a` and `b` are indeed compatible.
If it is `false`, we must use the full-check.
-/
partial def compatibleTypesQuick (a b : Expr) : Bool :=
  if a.isErased || b.isErased then
    true
  else
    let a' := a.headBeta
    let b' := b.headBeta
    if a != a' || b != b' then
      compatibleTypesQuick a' b'
    else if a == b then
      true
    else
      match a, b with
      -- Note that even after reducing to head-beta, we can still have `.app` terms. For example,
      -- an inductive constructor application such as `List Int`
      | .app f a, .app g b => compatibleTypesQuick f g && compatibleTypesQuick a b
      | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ => compatibleTypesQuick d₁ d₂ && compatibleTypesQuick b₁ b₂
      | .lam _ d₁ b₁ _, .lam _ d₂ b₂ _ => compatibleTypesQuick d₁ d₂ && compatibleTypesQuick b₁ b₂
      | .sort u, .sort v => Level.isEquiv u v
      | .const n us, .const m vs => n == m && List.isEqv us vs Level.isEquiv
      | _, _ => false

/--
Complete check for `compatibleTypes`. It eta-expands type formers. See comment at `compatibleTypes`.
-/
partial def InferType.compatibleTypesFull (a b : Expr) : InferTypeM Bool := do
  if a.isErased || b.isErased then
    return true
  else
    let a' := a.headBeta
    let b' := b.headBeta
    if a != a' || b != b' then
      compatibleTypesFull a' b'
    else if a == b then
      return true
    else
      match a, b with
      -- Note that even after reducing to head-beta, we can still have `.app` terms. For example,
      -- an inductive constructor application such as `List Int`
      | .app f a, .app g b => compatibleTypesFull f g <&&> compatibleTypesFull a b
      | .forallE n d₁ b₁ bi, .forallE _ d₂ b₂ _ =>
        unless (← compatibleTypesFull d₁ d₂) do return false
        withLocalDecl n d₁ bi fun x =>
          compatibleTypesFull (b₁.instantiate1 x) (b₂.instantiate1 x)
      | .lam n d₁ b₁ bi, .lam _ d₂ b₂ _ =>
        unless (← compatibleTypesFull d₁ d₂) do return false
        withLocalDecl n d₁ bi fun x =>
          compatibleTypesFull (b₁.instantiate1 x) (b₂.instantiate1 x)
      | .sort u, .sort v => return Level.isEquiv u v
      | .const n us, .const m vs => return n == m && List.isEqv us vs Level.isEquiv
      | _, _ =>
        if a.isLambda then
          let some b ← etaExpand? b | return false
          compatibleTypesFull a b
        else if b.isLambda then
          let some a ← etaExpand? a | return false
          compatibleTypesFull a b
        else
          return false
where
  etaExpand? (e : Expr) : InferTypeM (Option Expr) := do
    match (← inferType e).headBeta with
    | .forallE n d _ bi =>
      /-
      In principle, `.app e (.bvar 0)` may not be a valid LCNF type sub-expression
      because `d` may not be a type former type, See remark `compatibleTypes` for
      a justification why this is ok.
      -/
      return some (.lam n d (.app e (.bvar 0)) bi)
    | _ => return none

/--
Return true if the LCNF types `a` and `b` are compatible.
Remark: `a` and `b` can be type formers (e.g., `List`, or `fun (α : Type) => Nat → Nat × α`)
Remark: We may need to eta-expand type formers to establish whether they are compatible or not.
For example, suppose we have
```
fun (x : B) => Id B ◾ ◾
Id B ◾
```
We must eta-expand `Id B ◾` to `fun (x : B) => Id B ◾ x`. Note that, we use `x` instead of `◾` to
make the implementation simpler and skip the check whether `B` is a type former type. However,
this simplification should not affect correctness since `◾` is compatible with everything.
Remark: see comment at `isErasedCompatible`.
Remark: because of "erasure confusion" see note above, we assume `◾` (aka `lcErasure`) is compatible with everything.
This is a simplification. We used to use `isErasedCompatible`, but this only address item 1.
For item 2, we would have to modify the `toLCNFType` function and make sure a type former is erased if the expected
type is not always a type former (see `S.mk` type and example in the note above).
-/
def InferType.compatibleTypes (a b : Expr) : InferTypeM Bool := do
  if compatibleTypesQuick a b then
    return true
  else
    compatibleTypesFull a b

end Lean.Compiler.LCNF
