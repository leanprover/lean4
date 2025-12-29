/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
public import Lean.Meta.Tactic.Grind.AlphaShareBuilder
namespace Lean.Meta.Sym
/-!
A version of `replace_fn.h` that ensures the resulting expression is maximally shared.
-/
open Grind
abbrev M := StateT (Std.HashMap (ExprPtr × Nat) Expr) AlphaShareBuilderM

export Grind (AlphaShareBuilderM liftBuilderM)

def save (key : ExprPtr × Nat) (r : Expr) : M Expr := do
  modify fun cache => cache.insert key r
  return r

mutual
@[specialize] def visitChild (e : Expr) (offset : Nat) (f : Expr → Nat → AlphaShareBuilderM (Option Expr)) : M Expr := do
  let key := (⟨e⟩, offset)
  if let some r := (← get)[key]? then
    return r
  else if let some r ← f e offset then
    save key r
  else match e with
    | .lit _ | .mvar _ | .bvar _ | .fvar _ | .const _ _ | .sort _ => save key e
    | e => save key (← visit e offset f)

@[specialize] def visit (e : Expr) (offset : Nat) (fn : Expr → Nat → AlphaShareBuilderM (Option Expr)) : M Expr := do
  match e with
  | .lit _ | .mvar _ | .bvar _ | .fvar _ | .const _ _ | .sort _ => unreachable!
  | .app f a => mkAppS (← visitChild f offset fn) (← visitChild a offset fn)
  | .mdata m a => mkMDataS m (← visitChild a offset fn)
  | .proj s i a => mkProjS s i (← visitChild a offset fn)
  | .forallE n d b bi => mkForallS n bi (← visitChild d offset fn) (← visitChild b (offset+1) fn)
  | .lam n d b bi => mkLambdaS n bi (← visitChild d offset fn) (← visitChild b (offset+1) fn)
  | .letE n t v b d => mkLetS n (← visitChild t offset fn) (← visitChild v offset fn) (← visitChild b (offset+1) fn) (nondep := d)
end

/--
Similar to `replace_fn` in the kernel, but assumes input is maximally shared, and ensures
output is also maximally shared.
-/
@[inline] public def replaceS' (e : Expr) (f : Expr → Nat → AlphaShareBuilderM (Option Expr)) : AlphaShareBuilderM Expr := do
  if let some r ← f e 0 then
    return r
  match e with
  | .lit _ | .mvar _ | .bvar _ | .fvar _ | .const _ _ | .sort _ => return e
  | _ => visit e 0 f |>.run' {}

@[inline] public def replaceS (e : Expr) (f : Expr → Nat → AlphaShareBuilderM (Option Expr)) : SymM Expr := do
  liftBuilderM <| replaceS' e f

end Lean.Meta.Sym
