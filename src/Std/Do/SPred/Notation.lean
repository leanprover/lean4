/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license.
Authors: Lars König, Sebastian Graf
-/
module

prelude
public import Std.Do.SPred.SPred
meta import Init.NotationExtra

public @[expose] section

namespace Std.Do

open Lean Macro Parser PrettyPrinter

-- define `spred` embedding in `term`.
-- An explicit `spred` marker avoids exponential blowup in terms
-- that do not opt into the extended syntax.
scoped syntax:max "spred(" term ")" : term
scoped syntax:max "term(" term ")" : term

-- allow fallback to `term`
macro_rules
  | `(spred(term($t))) => pure t
  | `(spred($t))       => pure t

-- push `spred` inside some `term` constructs
macro_rules
  | `(spred(($P)))                  => ``((spred($P)))
  | `(spred(fun $xs* => $b))        => ``(fun $xs* => spred($b))
  | `(spred(if $c then $t else $e)) => ``(if $c then spred($t) else spred($e))
  | `(spred(($P : $t)))             => ``((spred($P) : $t))

/-- Remove an `spred` layer from a `term` syntax object. -/
-- inverts the rules above.
partial def SPred.Notation.unpack [Monad m] [MonadRef m] [MonadQuotation m] : Term → m Term
  | `(spred($P))             => do `($P)
  | `(($P))                  => do `(($(← unpack P)))
  | `(if $c then $t else $e) => do
    let t ← unpack t
    let e ← unpack e
    `(if $c then $t else $e)
  | `(fun $xs* => $b)        => do
    let b ← unpack b
    `(fun $xs* => $b)
  | `(($P : $t))             => do ``(($(← unpack P) : $t))
  | `($t)                    => `($t)

/-! # Idiom notation -/

/-- Embedding of pure Lean values into `SVal`. -/
scoped syntax "⌜" term "⌝" : term
/-- ‹t› in `SVal` idiom notation. Accesses the state of type `t`. -/
scoped syntax "‹" term "›ₛ" : term
/--
  Use getter `t : SVal σs σ` in `SVal` idiom notation; sugar for `SVal.uncurry t (by assumption)`.
-/
scoped syntax:max "#" term:max : term

/-! # Sugar for `SPred` -/

/-- Entailment in `SPred`; sugar for `SPred.entails`. -/
scoped syntax:25 term:26 " ⊢ₛ " term:25 : term
/-- Tautology in `SPred`; sugar for `SPred.entails ⌜True⌝`. -/
scoped syntax:25 "⊢ₛ " term:25 : term
/-- Bi-entailment in `SPred`; sugar for `SPred.bientails`. -/
scoped syntax:25 term:25 " ⊣⊢ₛ " term:25 : term

macro_rules
  | `(⌜$t⌝) => ``(SVal.curry (fun tuple => $t))
  | `(#$t) => `(SVal.uncurry $t (by assumption))
  | `(‹$t›ₛ) => `(#(SVal.getThe $t))
  | `($P ⊢ₛ $Q) => ``(SPred.entails spred($P) spred($Q))
  | `(spred($P ∧ $Q)) => ``(SPred.and spred($P) spred($Q))
  | `(spred($P ∨ $Q)) => ``(SPred.or spred($P) spred($Q))
  | `(spred(¬ $P)) => ``(SPred.not spred($P))
  | `(spred($P → $Q)) => ``(SPred.imp spred($P) spred($Q))
  | `(spred($P ↔ $Q)) => ``(SPred.iff spred($P) spred($Q))
  | `(spred(∃ $xs:explicitBinders, $P)) => do expandExplicitBinders ``SPred.exists xs (← `(spred($P)))
  | `(⊢ₛ $P) => ``(SPred.entails ⌜True⌝ spred($P))
  | `($P ⊣⊢ₛ $Q) => ``(SPred.bientails spred($P) spred($Q))
  -- Sadly, ∀ does not resently use expandExplicitBinders...
  | `(spred(∀ _%$tk, $P)) => ``(SPred.forall (fun _%$tk => spred($P)))
  | `(spred(∀ _%$tk : $ty, $P)) => ``(SPred.forall (fun _%$tk : $ty => spred($P)))
  | `(spred(∀ (_%$tk $xs* : $ty), $P)) => ``(SPred.forall (fun _%$tk : $ty => spred(∀ ($xs* : $ty), $P)))
  | `(spred(∀ $x:ident, $P)) => ``(SPred.forall (fun $x => spred($P)))
  | `(spred(∀ ($x:ident : $ty), $P)) => ``(SPred.forall (fun $x : $ty => spred($P)))
  | `(spred(∀ ($x:ident $xs* : $ty), $P)) => ``(SPred.forall (fun $x : $ty => spred(∀ ($xs* : $ty), $P)))
  | `(spred(∀ $x:ident $xs*, $P)) => ``(SPred.forall (fun $x => spred(∀ $xs*, $P)))
  | `(spred(∀ ($x:ident : $ty) $xs*, $P)) => ``(SPred.forall (fun $x : $ty => spred(∀ $xs*, $P)))
  | `(spred(∀ ($x:ident $xs* : $ty) $ys*, $P)) => ``(SPred.forall (fun $x : $ty => spred(∀ ($xs* : $ty) $ys*, $P)))

namespace SPred.Notation

@[app_unexpander SVal.curry]
meta def unexpandCurry : Unexpander
  | `($_ $t $ts*) => do
    match t with
    | `(fun $_ => $e) => if ts.isEmpty then ``(⌜$e⌝) else ``(⌜$e⌝ $ts*)
    | _ => throw ()
  | _ => throw ()

@[app_unexpander SVal.uncurry]
meta def unexpandUncurry : Unexpander
  | `($_ $f $ts*) => do
    match f with
    | `(SVal.getThe $t) => if ts.isEmpty then ``(‹$t›ₛ) else ``(‹$t›ₛ $ts*)
    | `($t) => if ts.isEmpty then ``(#$t) else ``(#$t $ts*)
  | _ => throw ()

@[app_unexpander SPred.entails]
meta def unexpandEntails : Unexpander
  | `($_ $P $Q)  => do
    let P ← unpack P; let Q ← unpack Q;
    match P with
    | `(⌜True⌝) => ``(⊢ₛ $Q)
    | _ => ``($P ⊢ₛ $Q)
  | _ => throw ()

@[app_unexpander SPred.bientails]
meta def unexpandBientails : Unexpander
  | `($_ $P $Q)  => do
    let P ← unpack P; let Q ← unpack Q;
    ``($P ⊣⊢ₛ $Q)
  | _ => throw ()

@[app_unexpander SPred.and]
meta def unexpandAnd : Unexpander
  | `($_ $P $Q) => do
    let P ← unpack P; let Q ← unpack Q;
    ``(spred($P ∧ $Q))
  | _ => throw ()

@[app_unexpander SPred.or]
meta def unexpandOr : Unexpander
  | `($_ $P $Q) => do
    let P ← unpack P; let Q ← unpack Q;
    ``(spred($P ∨ $Q))
  | _ => throw ()

@[app_unexpander SPred.not]
meta def unexpandNot : Unexpander
  | `($_ $P) => do
    let P ← unpack P;
    ``(spred(¬ $P))
  | _ => throw ()

@[app_unexpander SPred.imp]
meta def unexpandImp : Unexpander
  | `($_ $P $Q) => do
    let P ← unpack P; let Q ← unpack Q;
    ``(spred($P → $Q))
  | _ => throw ()

@[app_unexpander SPred.forall]
meta def unexpandForall : Unexpander
  | `($_ fun $x:ident => ∀ $y:ident $[$z:ident]*, $Ψ) => do
    let Ψ ← unpack Ψ
    ``(spred(∀ $x:ident $y:ident $[$z:ident]*, $Ψ))
  | `($_ fun $x:ident => $Ψ) => do
    let Ψ ← unpack Ψ
    ``(spred(∀ $x:ident, $Ψ))
  | _ => throw ()

@[app_unexpander SPred.exists]
meta def unexpandExists : Unexpander
  | `($_ fun $x:ident => ∃ $y:ident $[$z:ident]*, $Ψ) => do
    let Ψ ← unpack Ψ
    ``(spred(∃ $x:ident $y:ident $[$z:ident]*, $Ψ))
  | `($_ fun $x:ident => $Ψ) => do
    let Ψ ← unpack Ψ
    ``(spred(∃ $x:ident, $Ψ))
  | _ => throw ()

@[app_unexpander SPred.iff]
meta def unexpandIff : Unexpander
  | `($_ $P $Q) => do
    let P ← unpack P; let Q ← unpack Q;
    ``(spred($P ↔ $Q))
  | _ => throw ()
