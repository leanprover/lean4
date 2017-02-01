/-
Copyright (c) 2016 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/
prelude
import init.meta.format
import init.meta.expr
import init.data.string
import init.category.state

import init.native.internal
import init.native.ir
import init.native.format
import init.native.builtin
import init.native.util
import init.native.pass
import init.native.config

open native

@[reducible] meta def binding :=
  (name × expr × expr)

@[reducible] meta def anf_state :=
  (list (list binding) × nat)

@[reducible] meta def anf_monad :=
  state anf_state

meta def trace_anf (s : string) : anf_monad unit :=
  trace s (return ())

private meta def let_bind (n : name) (ty : expr) (e : expr) : anf_monad unit := do
  scopes ← state.read,
  match scopes with
  | ([], _) := return ()
  | ((s :: ss), count) := state.write $ (((n, ty, e) :: s) :: ss, count)
  end

private meta def mk_let : list binding → expr → expr
| [] body := body
| ((n, ty, val) :: es) body :=
  mk_let es (expr.elet n ty val (expr.abstract body (mk_local n)))

private meta def mk_let_in_current_scope (body : expr) : anf_monad expr := do
  (scopes, _) ← state.read,
  match scopes with
  | [] := pure $ body
  | (top :: _) := return $ mk_let top body
  end

private meta def enter_scope (action : anf_monad expr) : anf_monad expr := do
  (scopes, count) ← state.read,
  state.write ([] :: scopes, count),
  result ← action,
  bound_result ← mk_let_in_current_scope result,
  state.write (scopes, count),
  return bound_result

private meta def fresh_name : anf_monad name := do
  (ss, count) ← state.read,
  -- need to replace this with unique prefix as per our earlier conversation
  n ← pure $ name.mk_numeral (unsigned.of_nat count) `_anf_,
  state.write (ss, count + 1),
  return n

-- Hoist a set of expressions above the result of the callback
-- function.
meta def hoist
  (anf : expr → anf_monad expr)
  (kont : list name → anf_monad expr) : list expr → anf_monad expr
| [] := kont []
| es := do
     ns ← monad.for es $ (fun x, do
       value ← anf x,
       fresh ← fresh_name,
       let_bind fresh mk_neutral_expr value,
       return fresh),
     kont ns

private meta def anf_constructor (head : expr) (args : list expr) (anf : expr → anf_monad expr) : anf_monad expr :=
  hoist anf (fun args', return $ mk_call head (list.map mk_local args')) args

private meta def anf_call (head : expr) (args : list expr) (anf : expr → anf_monad expr) : anf_monad expr := do
  hoist anf (fun ns, match ns with
  -- need to think about how to refactor this, we should get at least one back from here always
  -- this case should never happen
  | [] := return head
  | (head' :: args') := return $ mk_call (mk_local head') (list.map mk_local args')
  end) (head :: args)

private meta def anf_case (action : expr → anf_monad expr) (e : expr) : anf_monad expr := do
  under_lambda fresh_name (fun e', enter_scope (action e')) e

private meta def anf_cases_on (head : expr) (args : list expr) (anf : expr → anf_monad expr) : anf_monad expr := do
  match args with
  | [] := return $ mk_call head []
  | (scrut :: cases) := do
    scrut' ← anf scrut,
    cases' ← monad.mapm (anf_case anf) cases,
    return $ mk_call head (scrut' :: cases')
  end

-- stop deleting this, not sure why I keep removing this line of code
open application_kind

private meta def anf' : expr → anf_monad expr
| (expr.elet n ty val body) := do
  fresh ← fresh_name,
  val' ← anf' val,
  let_bind fresh ty val',
  anf' (expr.instantiate_vars body [mk_local fresh])
| (expr.app f arg) := do
  let fn := expr.get_app_fn (expr.app f arg),
      args := expr.get_app_args (expr.app f arg)
   in match app_kind fn with
   | cases := anf_cases_on fn args anf'
   | constructor := anf_constructor fn args anf'
   | other := anf_call fn args anf'
   end
| e := return e

private meta def init_state : anf_state :=
  ([], 0)

private meta def anf_transform (conf : config) (e : expr) : expr :=
  prod.fst $ (under_lambda fresh_name (enter_scope ∘ anf') e) init_state

meta def anf : pass := {
  name := "anf",
  transform := fun conf proc, procedure.map_body (fun e, anf_transform conf e) proc
}
