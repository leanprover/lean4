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

import init.native.result
import init.native.internal
import init.native.builtin

meta def is_nat_cases_on (n : name) : bool :=
  decidable.to_bool $ `nat.cases_on = n

meta def is_cases_on (head : expr) : bool :=
  if is_nat_cases_on (expr.const_name head)
  then bool.tt
  else
  match native.is_internal_cases head with
  | option.some _ := bool.tt
  | option.none :=
    match native.get_builtin (expr.const_name head) with
    | option.some b :=
      match b with
      | builtin.cases _ _ := bool.tt
      | _ := bool.ff
      end
    | option.none := bool.ff
    end
  end

meta definition mk_local (n : name) : expr :=
  expr.local_const n n binder_info.default (expr.const n [])

meta def mk_neutral_expr : expr :=
  expr.const `_neutral_ []

meta def mk_call : expr → list expr → expr
| head [] := head
| head (e :: es) := mk_call (expr.app head e) es

-- really need to get out of the meta language so I can prove things, I should just have a unit test lemma
meta def under_lambda {M} [monad M] (fresh_name : M name) (action : expr -> M expr) : expr → M expr
| (expr.lam n bi ty body) := do
  fresh ← fresh_name,
  body' ← under_lambda $ expr.instantiate_var body (mk_local fresh),
  return $ expr.lam n bi ty (expr.abstract body' (mk_local fresh))
| e := action e

inductive application_kind
| cases
| constructor
| other

-- I like this pattern of hiding the annoying C++ interfaces
-- behind more typical FP constructs so we can do case analysis instead.
meta def app_kind (head : expr) : application_kind :=
if is_cases_on head
then application_kind.cases
else match native.is_internal_cnstr head with
| some _ := application_kind.constructor
| none := application_kind.other
end
