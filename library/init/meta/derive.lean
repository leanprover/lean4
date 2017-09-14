/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

Attribute that can automatically derive typeclass instances.
-/
prelude
import init.meta.attribute
import init.meta.interactive_base
import init.meta.mk_has_reflect_instance
import init.meta.mk_has_sizeof_instance
import init.meta.mk_inhabited_instance

open lean
open interactive.types
open tactic

/-- A handler that may or may not be able to implement the typeclass `cls` for `decl`.
    It should return `tt` if it was able to derive `cls` and `ff` if it does not know
    how to derive `cls`, in which case lower-priority handlers will be tried next. -/
meta def derive_handler := Π (cls : pexpr) (decl : name), tactic bool

@[user_attribute]
meta def derive_handler_attr : user_attribute :=
{ name := `derive_handler, descr := "register a definition of type `derive_handler` for use in the [derive] attribute" }

private meta def try_handlers (p : pexpr) (n : name) : list derive_handler → tactic unit
| []      := fail format!"failed to find a derive handler for '{p}'"
| (h::hs) :=
do success ← h p n,
   when (¬success) $
     try_handlers hs

@[user_attribute] meta def derive_attr : user_attribute unit (list pexpr) :=
{ name := `derive, descr := "automatically derive typeclass instances",
  parser := pexpr_list_or_texpr,
  after_set := some (λ n _ _,
  do ps ← derive_attr.get_param n,
     handlers ← attribute.get_instances `derive_handler,
     handlers ← handlers.mmap (λ n, eval_expr derive_handler (expr.const n [])),
     ps.mmap' (λ p, try_handlers p n handlers)) }

/-- Given a tactic `tac` that can solve an application of `cls` in the right context,
    `instance_derive_handler` uses it to build an instance declaration of `cls n`. -/
meta def instance_derive_handler (cls : name) (tac : tactic unit) (univ_poly := tt)
  (modify_target : name → list expr → expr → tactic expr := λ _ _, pure) : derive_handler :=
λ p n,
if p.is_constant_of cls then
do decl ← get_decl n,
   cls_decl ← get_decl cls,
   env ← get_env,
   guard (env.is_inductive n) <|> fail format!"failed to derive '{cls}', '{n}' is not an inductive type",
   let ls := decl.univ_params.map $ λ n, if univ_poly then level.param n else level.zero,
   -- incrementally build up target expression `Π (hp : p) [cls hp] ..., cls (n.{ls} hp ...)`
   -- where `p ...` are the inductive parameter types of `n`
   let tgt : expr := expr.const n ls,
   ⟨params, _⟩ ← mk_local_pis (decl.type.instantiate_univ_params (decl.univ_params.zip ls)),
   let tgt := tgt.mk_app params,
   tgt ← mk_app cls [tgt],
   tgt ← modify_target n params tgt,
   tgt ← params.enum.mfoldr (λ ⟨i, param⟩ tgt,
   do -- add typeclass hypothesis for each inductive parameter
      tgt ← do {
        guard $ i < env.inductive_num_params n,
        param_cls ← mk_app cls [param],
        -- TODO(sullrich): omit some typeclass parameters based on usage of `param`?
        pure $ expr.pi `a binder_info.inst_implicit param_cls tgt
      } <|> pure tgt,
      pure $ tgt.bind_pi param
   ) tgt,
   (_, val) ← tactic.solve_aux tgt (intros >> tac),
   val ← instantiate_mvars val,
   let trusted := decl.is_trusted ∧ cls_decl.is_trusted,
   add_decl (declaration.defn (n ++ cls)
             (if univ_poly then decl.univ_params else [])
             tgt val reducibility_hints.abbrev trusted),
   set_basic_attribute `instance (n ++ cls) tt,
   pure true
else pure false

@[derive_handler] meta def has_reflect_derive_handler :=
instance_derive_handler ``has_reflect mk_has_reflect_instance ff (λ n params tgt,
  -- add additional `reflected` assumption for each parameter
  params.mfoldr (λ param tgt,
  do param_cls ← mk_app `reflected [param],
    pure $ expr.pi `a binder_info.inst_implicit param_cls tgt
  ) tgt)

@[derive_handler] meta def has_sizeof_derive_handler :=
instance_derive_handler ``has_sizeof mk_has_sizeof_instance

attribute [derive has_reflect] bool prod sum option interactive.loc pos
