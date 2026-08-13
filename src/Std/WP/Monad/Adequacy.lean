/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.WP.Monad.Instances
universe u v w z
@[expose] public section

set_option linter.missingDocs true

open Lean.Order Std.WP

/-!
# Soundness Lemmas

These lemmas bridge `wp` reasoning to concrete program properties. Each one says:
if `wp prog ...` holds, then a property `P` holds of the program's result.
-/

namespace Std.WP

/-- Soundness for `Id`: if `wp prog P` holds, then `P` holds of the result. -/
theorem Id.of_wp_run_eq {α : Type u} {x : α} {prog : Id α}
  (h : Id.run prog = x) (P : α → Prop)
  (hwp : wp prog P EPost.Nil.mk) : P x := by
  rw [← h]
  exact hwp

/-- Soundness for `Option`: if `wp prog P` holds, then `P` holds of the result. -/
theorem Option.of_wp_eq {α : Type u} {x prog : Option α}
  (h : prog = x) (P : Option α → Prop)
  (hwp : wp prog (fun a => P (some a)) (P none)) : P x := by
  subst h
  cases prog with
  | none => exact hwp
  | some a => exact hwp

/-- Soundness for `StateM`: if `wp prog P s` holds, then `P` holds of `(prog.run s)`. -/
theorem StateM.of_wp_run_eq {x : α × σ} {prog : StateM σ α} {s : σ}
  (h : StateT.run prog s = x) (P : α × σ → Prop)
  (hwp : wp prog (fun a s' => P (a, s')) EPost.Nil.mk s) : P x := by
  rw [← h]
  exact hwp

/-- Soundness for `StateM` (discarding final state). -/
theorem StateM.of_wp_run'_eq {α σ : Type} {x : α} {prog : StateM σ α} {s : σ}
  (h : StateT.run' prog s = x) (P : α → Prop)
  (hwp : wp prog (fun a _ => P a) EPost.Nil.mk s) : P x := by
  rw [← h]
  exact hwp

/-- Soundness for `ReaderM`: if `wp prog P r` holds, then `P` holds of `(prog.run r)`. -/
theorem ReaderM.of_wp_run_eq {α ρ : Type} {x : α} {prog : ReaderM ρ α} {r : ρ}
  (h : ReaderT.run prog r = x) (P : α → Prop)
  (hwp : wp prog (fun a _ => P a) EPost.Nil.mk r) : P x := by
  rw [← h]
  exact hwp

/-- Soundness for `Except`: if `wp prog P` holds, then `P` holds of the result. -/
theorem Except.of_wp_eq {ε α : Type} {x prog : Except ε α}
  (h : prog = x) (P : Except ε α → Prop)
  (hwp : wp prog (fun a => P (.ok a)) epost⟨fun e => P (.error e)⟩) : P x := by
  subst h
  cases prog with
  | ok a => simpa only [wp] using! hwp
  | error e => simpa only [wp] using! hwp

/-- Soundness for `EStateM`: if `wp prog P s` holds, then `P` holds of `(prog.run s)`. -/
theorem EStateM.of_wp_run_eq {ε σ α : Type} {x : EStateM.Result ε σ α}
  {prog : EStateM ε σ α} {s : σ}
  (h : EStateM.run prog s = x) (P : EStateM.Result ε σ α → Prop)
  (hwp : wp prog (fun a s' => P (.ok a s')) (fun e s' => P (.error e s')) s) :
    P x := by
  rw [← h]
  change P (prog s)
  cases heq : prog s with
  | ok a s' =>
    simpa [wp, WP.wpTrans, heq] using hwp
  | error e s' =>
    simpa [wp, WP.wpTrans, heq] using hwp

end Std.WP
