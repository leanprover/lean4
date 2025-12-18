/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license.
Authors: Lars König, Sebastian Graf
-/
module

prelude
public import Std.Do.SPred.SPred
public meta import Std.Do.SPred.Notation.Basic

public section

set_option linter.missingDocs true

namespace Std.Do

open Lean Macro Parser PrettyPrinter

/-! # Idiom notation -/

/-- Embedding of pure Lean values into `SVal`. An alias for `SPred.pure`. -/
scoped syntax "⌜" term "⌝" : term

/-! # Sugar for `SPred` -/

/-- Entailment in `SPred`; sugar for `SPred.entails`. -/
scoped syntax:25 term:26 " ⊢ₛ " term:25 : term
/-- Tautology in `SPred`; sugar for `SPred.entails ⌜True⌝`. -/
scoped syntax:25 "⊢ₛ " term:25 : term
/-- Bi-entailment in `SPred`; sugar for `SPred.bientails`. -/
scoped syntax:25 term:25 " ⊣⊢ₛ " term:25 : term

macro_rules
  | `(⌜$t⌝) => ``(SPred.pure $t)
  | `($P ⊢ₛ $Q) => ``(SPred.entails spred($P) spred($Q))
  | `(spred($P ∧ $Q)) => ``(SPred.and spred($P) spred($Q))
  | `(spred($P ∨ $Q)) => ``(SPred.or spred($P) spred($Q))
  | `(spred(¬ $P)) => ``(SPred.not spred($P))
  | `(spred($P → $Q)) => ``(SPred.imp spred($P) spred($Q))
  | `(spred($P ↔ $Q)) => ``(SPred.iff spred($P) spred($Q))
  | `(spred(∃ $xs:explicitBinders, $P)) => do expandExplicitBinders ``SPred.exists xs (← `(spred($P)))
  | `(⊢ₛ $P) => ``(SPred.entails ⌜True⌝ spred($P))
  | `($P ⊣⊢ₛ $Q) => ``(SPred.bientails spred($P) spred($Q))
  -- Sadly, ∀ does not presently use expandExplicitBinders...
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

/--
Unexpander that reconstructs `⌜...⌝` syntax from applications of `SPred.pure`.
-/
@[app_unexpander SPred.pure]
meta def unexpandPure : Unexpander
  | `($_ $t $ts*) => do
    if ts.isEmpty then ``(⌜$t⌝) else ``(⌜$t⌝ $ts*)
  | _ => throw ()

/--
Unexpander that reconstructs `... ⊢ₛ ...⌝` syntax from applications of `SPred.entails`.
-/
@[app_unexpander SPred.entails]
meta def unexpandEntails : Unexpander
  | `($_ $P $Q)  => do
    let P ← unpack P; let Q ← unpack Q;
    match P with
    | `(⌜True⌝) => ``(⊢ₛ $Q)
    | _ => ``($P ⊢ₛ $Q)
  | _ => throw ()

/--
Unexpander that reconstructs `... ⊣⊢ₛ ...⌝` syntax from applications of `SPred.entails`.
-/
@[app_unexpander SPred.bientails]
meta def unexpandBientails : Unexpander
  | `($_ $P $Q)  => do
    let P ← unpack P; let Q ← unpack Q;
    ``($P ⊣⊢ₛ $Q)
  | _ => throw ()

/--
Unexpander that reconstructs `spred(... ∧ ...)⌝` syntax from applications of `SPred.and`, lifting
nested applications of `spred(...)` from the arguments.
-/
@[app_unexpander SPred.and]
meta def unexpandAnd : Unexpander
  | `($_ $P $Q) => do
    let P ← unpack P; let Q ← unpack Q;
    ``(spred($P ∧ $Q))
  | _ => throw ()

/--
Unexpander that reconstructs `spred(... ∨ ...)⌝` syntax from applications of `SPred.or`, lifting
nested applications of `spred(...)` from the arguments.
-/
@[app_unexpander SPred.or]
meta def unexpandOr : Unexpander
  | `($_ $P $Q) => do
    let P ← unpack P; let Q ← unpack Q;
    ``(spred($P ∨ $Q))
  | _ => throw ()

/--
Unexpander that reconstructs `spred(¬ ...)⌝` syntax from applications of `SPred.not`, lifting
nested applications of `spred(...)` from the argument.
-/
@[app_unexpander SPred.not]
meta def unexpandNot : Unexpander
  | `($_ $P) => do
    let P ← unpack P;
    ``(spred(¬ $P))
  | _ => throw ()

/--
Unexpander that reconstructs `spred(... → ...)⌝` syntax from applications of `SPred.imp`, lifting
nested applications of `spred(...)` from the arguments.
-/
@[app_unexpander SPred.imp]
meta def unexpandImp : Unexpander
  | `($_ $P $Q) => do
    let P ← unpack P; let Q ← unpack Q;
    ``(spred($P → $Q))
  | _ => throw ()

/--
Unexpander that reconstructs `spred(∀ ..., ...)⌝` syntax from applications of `SPred.forall`, lifting
nested applications of `spred(...)` from the body.
-/
@[app_unexpander SPred.forall]
meta def unexpandForall : Unexpander
  | `($_ fun $x:ident => ∀ $y:ident $[$z:ident]*, $Ψ) => do
    let Ψ ← unpack Ψ
    ``(spred(∀ $x:ident $y:ident $[$z:ident]*, $Ψ))
  | `($_ fun $x:ident => $Ψ) => do
    let Ψ ← unpack Ψ
    ``(spred(∀ $x:ident, $Ψ))
  | _ => throw ()

/--
Unexpander that reconstructs `spred(∃ ..., ...)⌝` syntax from applications of `SPred.exists`, lifting
nested applications of `spred(...)` from the body.
-/
@[app_unexpander SPred.exists]
meta def unexpandExists : Unexpander
  | `($_ fun $x:ident => ∃ $y:ident $[$z:ident]*, $Ψ) => do
    let Ψ ← unpack Ψ
    ``(spred(∃ $x:ident $y:ident $[$z:ident]*, $Ψ))
  | `($_ fun $x:ident => $Ψ) => do
    let Ψ ← unpack Ψ
    ``(spred(∃ $x:ident, $Ψ))
  | _ => throw ()

/--
Unexpander that reconstructs `spred(... ↔ ...)⌝` syntax from applications of `SPred.iff`, lifting
nested applications of `spred(...)` from the arguments.
-/
@[app_unexpander SPred.iff]
meta def unexpandIff : Unexpander
  | `($_ $P $Q) => do
    let P ← unpack P; let Q ← unpack Q;
    ``(spred($P ↔ $Q))
  | _ => throw ()
