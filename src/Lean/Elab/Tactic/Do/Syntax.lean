/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
prelude
import Init.NotationExtra
import Lean.Elab.BuiltinNotation
import Std.Do.PostCond
import Std.Do.Triple.Basic

namespace Std.Do

open Lean Parser Meta Elab Term

def post_syntax := leading_parser
  "post⟨" >> withoutPosition (withoutForbidden (sepBy termParser ", " (allowTrailingSep := true))) >> "⟩"
scoped syntax:max "post⟨" term,+ "⟩" : term
macro_rules | `(post⟨$handlers,*⟩) => `(by exact ⟨$handlers,*, ()⟩)
  -- NB: Postponement through by exact is the entire point of this macro
  -- until https://github.com/leanprover/lean4/pull/8074 lands
example : PostCond Nat .pure := post⟨fun s => True⟩
example : PostCond (Nat × Nat) (PostShape.except Nat (PostShape.arg Nat PostShape.pure)) :=
  post⟨fun (r, xs) s => r ≤ 4 ∧ s = 4 ∧ r + xs > 4, fun e s => e = 42 ∧ s = 4⟩

open Lean Parser Term in
def funArrow : Parser := unicodeSymbol " ↦ " " => "
@[inherit_doc PostCond.total]
scoped macro "⇓" xs:Lean.Parser.Term.funBinder+ funArrow e:term : term =>
  `(PostCond.total (by exact (fun $xs* => spred($e)))) -- NB: Postponement through by exact

@[app_unexpander PostCond.total]
private def unexpandPostCondTotal : PrettyPrinter.Unexpander
  | `($_ fun $xs* => $e) => do `(⇓ $xs* => $(← SPred.Notation.unpack e))
  | _ => throw ()

elab_rules : term
  | `(⦃$P⦄ $x ⦃$Q⦄) => do
    -- In a simple world, this would just be a macro expanding to
    -- `Triple $x spred($P) spred($Q)`.
    -- However, currently we need to help type inference for P and Q.
    -- Specifically, if `x : StateT σ m α`, `[wp : WP m ps]` and `P : σ → Assertion ps`,
    -- then `Triple x P _` will not elaborate because `σ → Assertion ps =?= Assertion ?ps` fails.
    -- We must first instantiate `?ps` to `.arg σ ps` through the `outParam` of `WP`, hence this elaborator.
    -- This is tracked in #8766, and #8074 might be a fix.
    let x ← elabTerm x none
    let ty ← inferType x
    tryPostponeIfMVar ty
    let ty ← instantiateMVars ty
    let .app m α := ty.consumeMData | throwError "Not a type application {ty}"
    let some u ← Level.dec <$> getLevel ty | throwError "Wrong level 0 {ty}"
    let ps ← mkFreshExprMVar (mkConst ``PostShape)
    let inst ← synthInstance (mkApp2 (mkConst ``WP [u]) m ps)
    let P ← elabTerm (← `(spred($P))) (mkApp (mkConst ``Assertion) ps)
    let Q ← elabTerm (← `(spred($Q))) (mkApp2 (mkConst ``PostCond) α ps)
    return mkApp7 (mkConst ``Triple [u]) m ps inst α x P Q

@[app_unexpander Triple]
private def unexpandTriple : PrettyPrinter.Unexpander
  | `($_ $x $P $Q) => do
    `(⦃$(← SPred.Notation.unpack P)⦄ $x ⦃$Q⦄)
  | _ => throw ()
