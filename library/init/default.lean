/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.core init.logic init.category init.data.basic
import init.propext init.funext init.category.combinators init.function init.classical
import init.timeit init.trace init.coe init.wf init.meta init.instances
import init.algebra init.data

def debugger.attr : user_attribute :=
{ name  := `breakpoint,
  descr := "breakpoint for debugger" }

run_command attribute.register `debugger.attr

open tactic
/-
  Define id_locked using meta-programming because we don't have
  syntax for setting reducibility_hints.

  See module init.meta.declaration.
-/
run_command do
 l  ← return $ level.param `l,
 Ty ← return $ expr.sort l,
 type ← to_expr `(Π {α : %%Ty}, α → α),
 val  ← to_expr `(λ {α : %%Ty} (a : α), a),
 add_decl (declaration.defn `id_locked [`l] type val reducibility_hints.opaque tt)

lemma {u} id_locked_eq {α : Type u} (a : α) : id_locked a = a :=
rfl
