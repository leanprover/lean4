/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Elaborator for the Lean language: takes commands and produces side effects
-/
prelude
import init.lean.parser.module
import init.lean.expander
import init.lean.expr
import init.lean.options

namespace lean
-- TODO(Sebastian): should probably be meta together with the whole elaborator
constant environment : Type
@[extern "lean_environment_mk_empty"]
constant environment.mk_empty : unit → environment
@[extern "lean_environment_contains"]
constant environment.contains : (@& environment) → (@& name) → bool
-- deprecated constructor
@[extern "lean_expr_local"]
constant expr.local : name → name → expr → binder_info → expr

namespace elaborator
-- TODO(Sebastian): move
-- TODO(Sebastian): should be its own monad?
structure name_generator :=
(«prefix» : name)
(next_idx : uint32)

structure section_var :=
(uniq_name : name)
(binder_info : binder_info)
(type : expr)

/-- Simplified state of the Lean 3 parser. Maps are replaced with lists for easier interop. -/
structure old_elaborator_state :=
(env : environment)
(ngen : name_generator)
(univs : list (name × level))
(vars : list (name × section_var))
(include_vars : list name)
(options : options)
(next_inst_idx : nat)
(ns : name)

@[extern "lean_elaborator_elaborate_command"]
constant elaborate_command (filename : @& string) : expr → (@& old_elaborator_state) →
  option old_elaborator_state × message_log

open parser
open parser.combinators
open parser.term
open parser.command
open parser.command.notation_spec
open expander

local attribute [instance] name.has_lt_quick

-- TODO(Sebastian): move
/-- An rbmap that remembers the insertion order. -/
structure ordered_rbmap (α β : Type) (lt : α → α → Prop) :=
(entries : list (α × β))
(map : rbmap α (nat × β) lt)
(size : nat)

namespace ordered_rbmap
variables {α β : Type} {lt : α → α → Prop} [decidable_rel lt] (m : ordered_rbmap α β lt)

def empty : ordered_rbmap α β lt := {entries := [], map := mk_rbmap _ _ _, size := 0}

def insert (k : α) (v : β) : ordered_rbmap α β lt :=
{entries := (k, v)::m.entries, map := m.map.insert k (m.size, v), size := m.size + 1}

def find (a : α) : option (nat × β) :=
m.map.find a

def of_list (l : list (α × β)) : ordered_rbmap α β lt :=
l.foldl (λ m p, ordered_rbmap.insert m (prod.fst p) (prod.snd p)) ordered_rbmap.empty
end ordered_rbmap

structure elaborator_config extends frontend_config :=
(initial_parser_cfg : module_parser_config)

instance elaborator_config_coe_frontend_config : has_coe elaborator_config frontend_config :=
⟨elaborator_config.to_frontend_config⟩

/-- Elaborator state that will be reverted at the end of a section or namespace. -/
structure scope :=
-- "section" or "namespace" (or "MODULE"), currently
(cmd : string)
-- Scope header, should match identifier after `end`. Can be `name.anonymous` for sections.
(header : name)
(notations : list notation_macro := [])
/- The set of local universe variables.
   We remember their insertion order so that we can keep the order when copying them to declarations. -/
(univs : ordered_rbmap name level (<) := ordered_rbmap.empty)
/- The set of local variables. -/
(vars : ordered_rbmap name section_var (<) := ordered_rbmap.empty)
/- The subset of `vars` that is tagged as always included. -/
(include_vars : rbtree name (<) := mk_rbtree _ _)
/- The stack of nested active `namespace` commands. -/
(ns_stack : list name := [])
/- The set of active `open` declarations. -/
(open_decls : list open_spec.view := [])
(options : options := options.mk)

/-- An `export` command together with the namespace it was declared in. Opening the namespace activates
    the export. -/
structure scoped_export_decl :=
(in_ns : name)
(spec : open_spec.view)

structure elaborator_state :=
-- TODO(Sebastian): retrieve from environment
(reserved_notations : list reserve_notation.view := [])
(notations : list notation_macro := [])
(notation_counter := 0)
/- The current set of `export` declarations (active or inactive). -/
(export_decls : list scoped_export_decl := [])

-- Stack of current scopes. The bottom-most scope is the module scope.
(scopes : list scope)
(messages : message_log := message_log.empty)
(parser_cfg : module_parser_config)
(expander_cfg : expander.expander_config)
(env : environment := environment.mk_empty ())
(ngen : name_generator)
(next_inst_idx : nat := 0)

@[derive monad monad_rec monad_reader monad_state monad_except]
def elaborator_m := rec_t syntax unit $ reader_t elaborator_config $ state_t elaborator_state $ except_t message id
abbreviation elaborator := syntax → elaborator_m unit

/-- Recursively elaborate any command. -/
def command.elaborate : elaborator := recurse

def current_scope : elaborator_m scope := do
  st ← get,
  match st.scopes with
  | [] := error none "current_scope: unreachable"
  | sc::_ := pure sc

def modify_current_scope (f : scope → scope) : elaborator_m unit := do
  st ← get,
  match st.scopes with
  | [] := error none "modify_current_scope: unreachable"
  | sc::scs := put {st with scopes := f sc::scs}

def mangle_ident (id : syntax_ident) : name :=
id.scopes.foldl name.mk_numeral id.val

def level_get_app_args : syntax → elaborator_m (syntax × list syntax)
| stx := do
  match stx.kind with
  | some level.leading := pure (stx, [])
  | some level.trailing := (match view level.trailing stx with
    | level.trailing.view.app lta := do
      (fn, args) ← level_get_app_args lta.fn,
      pure (fn, lta.arg :: args)
    | level.trailing.view.add_lit _ := pure (stx, []))
  | _ := error stx $ "level_get_app_args: unexpected input: " ++ to_string stx

def level_add : level → nat → level
| l 0     := l
| l (n+1) := (level_add l n).succ

def to_level : syntax → elaborator_m level
| stx := do
  (fn, args) ← level_get_app_args stx,
  sc ← current_scope,
  match fn.kind with
  | some level.leading := (match view level.leading fn, args with
    | level.leading.view.hole _, [] := pure $ level.mvar name.anonymous
    | level.leading.view.lit lit, [] := pure $ level.of_nat lit.to_nat
    | level.leading.view.var id, [] := let id := mangle_ident id in (match sc.univs.find id with
      | some _ := pure $ level.param id
      | none   := error stx $ "unknown universe variable '" ++ to_string id ++ "'")
    | level.leading.view.max _, (arg::args) := list.foldr level.max <$> to_level arg <*> args.mmap to_level
    | level.leading.view.imax _, (arg::args) := list.foldr level.imax <$> to_level arg <*> args.mmap to_level
    | _, _ := error stx "ill-formed universe level")
  | some level.trailing := (match view level.trailing fn, args with
    | level.trailing.view.add_lit lta, [] := do
      l ← to_level lta.lhs,
      pure $ level_add l lta.rhs.to_nat
    | _, _ := error stx "ill-formed universe level")
  | _ := error stx $ "to_level: unexpected input: " ++ to_string stx

def expr.mk_annotation (ann : name) (e : expr) :=
expr.mdata (kvmap.set_name {} `annotation ann) e

def dummy : expr := expr.const `Prop []

def mk_eqns (type : expr) (eqns : list (name × list expr × expr)): expr :=
  let eqns := eqns.map $ λ ⟨fn, lhs, rhs⟩, do {
    let fn := expr.local fn fn type binder_info.aux_decl,
    let lhs := expr.mk_app (expr.mk_annotation `@ fn) lhs,
    expr.app lhs rhs
  } in
  expr.mk_annotation `pre_equations $ expr.mk_capp `_ eqns

def to_pexpr : syntax → elaborator_m expr
| stx@(syntax.raw_node {kind := k, args := args}) := do
  e ← match k with
  | @ident_univs := do
    let v := view ident_univs stx,
    e ← match v with
    | {id := id, univs := some univs} := expr.const (mangle_ident id) <$> univs.levels.mmap to_level
    | {id := id, univs := none}       := pure $ expr.const (mangle_ident id) [],
    let m := kvmap.set_name {} `annotation `preresolved,
    let m := v.id.preresolved.enum.foldl (λ m ⟨i, n⟩, kvmap.set_name m (name.anonymous.mk_numeral i) n) m,
    pure $ expr.mdata m e
  | @app   := let v := view app stx in
    expr.app <$> to_pexpr v.fn <*> to_pexpr v.arg
  | @lambda := do
    let lam := view lambda stx,
    binders.view.simple bnder ← pure lam.binders
      | error stx "ill-formed lambda",
    (bi, id, type) ← pure bnder.to_binder_info,
    expr.lam (mangle_ident id) bi <$> to_pexpr type <*> to_pexpr lam.body
  | @pi := do
    let v := view pi stx,
    binders.view.simple bnder ← pure v.binders
      | error stx "ill-formed pi",
    (bi, id, type) ← pure bnder.to_binder_info,
    expr.pi (mangle_ident id) bi <$> to_pexpr type <*> to_pexpr v.range
  | @sort := (match view sort stx with
    | sort.view.Sort _ := pure $ expr.sort level.zero
    | sort.view.Type _ := pure $ expr.sort $ level.succ level.zero)
  | @sort_app := do
    let v := view sort_app stx,
    (match view sort v.fn with
     | sort.view.Sort _ := expr.sort <$> to_level v.arg
     | sort.view.Type _ := (expr.sort ∘ level.succ) <$> to_level v.arg)
  | @anonymous_constructor := do
    let v := view anonymous_constructor stx,
    p ← to_pexpr $ mk_app (review hole {}) (v.args.map sep_by.elem.view.item),
    pure $ expr.mk_annotation `anonymous_constructor p
  | @hole := pure $ expr.mvar name.anonymous dummy
  | @«have» := do
    let v := view «have» stx,
    let id := (mangle_ident <$> opt_ident.view.id <$> v.id).get_or_else `this,
    let proof := match v.proof with
    | have_proof.view.term hpt := hpt.term
    | have_proof.view.from hpf := hpf.from.proof,
    lam ← expr.lam id binder_info.default <$> to_pexpr v.prop <*> to_pexpr v.body,
    expr.app (expr.mk_annotation `have lam) <$> to_pexpr proof
  | @«show» := do
    let v := view «show» stx,
    prop ← to_pexpr v.prop,
    proof ← to_pexpr v.from.proof,
    pure $ expr.mk_annotation `show $ expr.app (expr.lam `this binder_info.default prop $ expr.bvar 0) proof
  | @«let» := do
    let v := view «let» stx,
    let_lhs.view.id {id := id, binders := [], type := some ty} ← pure v.lhs
      | error stx "ill-formed let",
    expr.elet (mangle_ident id) <$> to_pexpr ty.type <*> to_pexpr v.value <*> to_pexpr v.body
  | @projection := do
    let v := view projection stx,
    let val := match v.proj with
    | projection_spec.view.id id := data_value.of_name id.val
    | projection_spec.view.num n := data_value.of_nat n.to_nat,
    expr.mdata (kvmap.insert {} `field_notation val) <$> to_pexpr v.term
  | @explicit := do
    let v := view explicit stx,
    let ann := match v.mod with
    | explicit_modifier.view.explicit _         := `@
    | explicit_modifier.view.partial_explicit _ := `@@,
    expr.mk_annotation ann <$> to_pexpr (review ident_univs v.id)
  | @inaccessible := do
    let v := view inaccessible stx,
    expr.mk_annotation `innaccessible <$> to_pexpr v.term  -- sic
  | @borrowed := do
    let v := view borrowed stx,
    expr.mk_annotation `borrowed <$> to_pexpr v.term
  | @number := do
    let v := view number stx,
    pure $ expr.lit $ literal.nat_val v.to_nat
  | @string_lit := do
    let v := view string_lit stx,
    pure $ expr.lit $ literal.str_val (v.value.get_or_else "NOT_A_STRING")
  | @choice := do
    last::rev ← list.reverse <$> args.mmap (λ a, to_pexpr a)
      | error stx "ill-formed choice",
    pure $ expr.mdata (kvmap.set_nat {} `choice args.length) $
      rev.reverse.foldr expr.app last
  | @struct_inst := do
    let v := view struct_inst stx,
    -- order should be: fields*, sources*, catchall?
    let (fields, other) := v.items.span (λ it, ↑match sep_by.elem.view.item it with
      | struct_inst_item.view.field _ := tt
      | _ := ff),
    let (sources, catchall) := other.span (λ it, ↑match sep_by.elem.view.item it with
      | struct_inst_item.view.source {source := some _} := tt
      | _ := ff),
    catchall ← match catchall with
    | [] := pure ff
    | [{item := struct_inst_item.view.source _}] := pure tt
    | {item := it}::_ := error (review struct_inst_item it) $ "unexpected item in structure instance notation",

    fields ← fields.mmap (λ f, match sep_by.elem.view.item f with
      | struct_inst_item.view.field f :=
        expr.mdata (kvmap.set_name {} `field $ mangle_ident f.id) <$> to_pexpr f.val
      | _ := error stx "to_pexpr: unreachable"),
    sources ← sources.mmap (λ src, match sep_by.elem.view.item src with
      | struct_inst_item.view.source {source := some src} := to_pexpr src
      | _ := error stx "to_pexpr: unreachable"),
    sources ← match v.with with
    | none     := pure sources
    | some src := do { src ← to_pexpr src.source, pure $ sources ++ [src]},

    let m := kvmap.set_nat {} "structure instance" fields.length,
    let m := kvmap.set_bool m `catchall catchall,
    let m := kvmap.set_name m `struct $
      (mangle_ident <$> struct_inst_type.view.id <$> v.type).get_or_else name.anonymous,
    let dummy := expr.sort level.zero,
    pure $ expr.mdata m $ (fields ++ sources).foldr expr.app dummy
  | @«match» := do
    let v := view «match» stx,
    eqns ← (v.equations.map sep_by.elem.view.item).mmap $ λ (eqn : match_equation.view), do {
      lhs ← eqn.lhs.mmap $ λ l, to_pexpr l.item,
      rhs ← to_pexpr eqn.rhs,
      pure (`_match_fn, lhs, rhs)
    },
    type ← to_pexpr $ get_opt_type v.type,
    let eqns := mk_eqns type eqns,
    expr.mdata mdata e ← pure eqns
      | error stx "to_pexpr: unreachable",
    let eqns := expr.mdata (mdata.set_bool `match tt) e,
    expr.mk_app eqns <$> v.scrutinees.mmap (λ scr, to_pexpr scr.item)
  | _ := error stx $ "to_pexpr: unexpected node: " ++ to_string k.name,
  (match k with
  | @app := pure e -- no position
  | _ := do
    cfg ← read,
    match stx.get_pos with
    | some pos :=
      let pos := cfg.file_map.to_position pos in
      pure $ expr.mdata ((kvmap.set_nat {} `column pos.column).set_nat `row pos.line) e
    | none := pure e)
| stx := error stx $ "to_pexpr: unexpected: " ++ to_string stx

/-- Returns the active namespace, that is, the concatenation of all active `namespace` commands. -/
def get_namespace : elaborator_m name := do
  sc ← current_scope,
  pure $ match sc.ns_stack with
  | ns::_ := ns
  | _     := name.anonymous

def old_elab_command (stx : syntax) (cmd : expr) : elaborator_m unit :=
do cfg ← read,
   let pos := cfg.file_map.to_position $ stx.get_pos.get_or_else (default _),
   let cmd := match cmd with
   | expr.mdata m e := expr.mdata ((kvmap.set_nat m `column pos.column).set_nat `row pos.line) e
   | e := e,
   st ← get,
   sc ← current_scope,
   ns ← get_namespace,
   let (st', msgs) := elaborate_command cfg.filename cmd {
     ns := ns,
     univs := sc.univs.entries.reverse,
     vars := sc.vars.entries.reverse,
     include_vars := sc.include_vars.to_list,
     options := sc.options,
     ..st},
   match st' with
   | some st' := do modify_current_scope $ λ sc, {sc with
       univs := ordered_rbmap.of_list st'.univs,
       vars := ordered_rbmap.of_list st'.vars,
       include_vars := rbtree.of_list st'.include_vars,
       options := st'.options,
     },
     modify $ λ st, {..st', ..st}
   | none := pure (),  -- error
   modify $ λ st, {st with messages := st.messages ++ msgs}

def names_to_pexpr (ns : list name) : expr :=
expr.mk_capp `_ $ ns.map (λ n, expr.const n [])

def attrs_to_pexpr (attrs : list (sep_by.elem.view attr_instance.view (option syntax_atom))) : elaborator_m expr :=
expr.mk_capp `_ <$> attrs.mmap (λ attr,
  expr.mk_capp attr.item.name.val <$> attr.item.args.mmap to_pexpr)

def decl_modifiers_to_pexpr (mods : decl_modifiers.view) : elaborator_m expr := do
  let mdata : kvmap := {},
  let mdata := match mods.doc_comment with
    | some {doc := some doc, ..} := mdata.set_string `doc_string doc.val
    | _ := mdata,
  let mdata := match mods.visibility with
    | some (visibility.view.private _) := mdata.set_bool `private tt
    | some (visibility.view.protected _) := mdata.set_bool `protected tt
    | _ := mdata,
  let mdata := mdata.set_bool `noncomputable mods.noncomputable.is_some,
  let mdata := mdata.set_bool `meta mods.meta.is_some,
  expr.mdata mdata <$> attrs_to_pexpr (match mods.attrs with
    | some attrs := attrs.attrs
    | none       := [])

def ident_univ_params_to_pexpr (id : ident_univ_params.view) : expr :=
expr.const (mangle_ident id.id) $ match id.univ_params with
  | some params := params.params.map (level.param ∘ mangle_ident)
  | none        := []

/-- Execute `elab` and reset local scope (universes, ...) after it has finished. -/
def locally (elab : elaborator_m unit) :
  elaborator_m unit := do
  sc ← current_scope,
  elab,
  modify_current_scope $ λ _, sc

def simple_binders_to_pexpr (bindrs : list simple_binder.view) : elaborator_m expr :=
expr.mk_capp `_ <$> bindrs.mmap (λ b, do
  let (bi, id, type) := b.to_binder_info,
  let id := mangle_ident id,
  type ← to_pexpr type,
  pure $ expr.local id id type bi)

def elab_def_like (stx : syntax) (mods : decl_modifiers.view) (dl : def_like.view) (kind : nat) : elaborator_m unit :=
match dl with
| {sig := {params := bracketed_binders.view.simple bbs}, ..} := do
  let mdata := kvmap.set_name {} `command `defs,
  mods ← decl_modifiers_to_pexpr mods,
  let kind := expr.lit $ literal.nat_val kind,
  match dl.old_univ_params with
  | some uparams :=
    modify_current_scope $ λ sc, {sc with univs :=
      (uparams.ids.map mangle_ident).foldl (λ m id, ordered_rbmap.insert m id (level.param id)) sc.univs}
  | none := pure (),
  -- do we actually need this??
  let uparams := names_to_pexpr $ match dl.old_univ_params with
  | some uparams := uparams.ids.map mangle_ident
  | none := [],
  let id := mangle_ident dl.name.id,
  let type := get_opt_type dl.sig.type,
  type ← to_pexpr type,
  let fns := expr.mk_capp `_ [expr.local id id type binder_info.aux_decl],
  val ← match dl.val with
  | decl_val.view.simple val  := to_pexpr val.body
  | decl_val.view.empty_match _ := pure $ mk_eqns type []
  | decl_val.view.match eqns  := do {
    eqns ← eqns.mmap (λ (eqn : equation.view), do
      lhs ← eqn.lhs.mmap to_pexpr,
      rhs ← to_pexpr eqn.rhs,
      pure (id, lhs, rhs)
    ),
    pure $ mk_eqns type eqns
  },
  params ← simple_binders_to_pexpr bbs,
  old_elab_command stx $ expr.mdata mdata $ expr.mk_capp `_ [mods, kind, uparams, fns, params, val]
| _ := error stx "elab_def_like: unexpected input"

def infer_mod_to_pexpr (mod : option infer_modifier.view) : expr :=
expr.lit $ literal.nat_val $ match mod with
| none := 0
| some $ infer_modifier.view.relaxed _ := 1
| some $ infer_modifier.view.strict _  := 2

def declaration.elaborate : elaborator :=
λ stx, locally $ do
  let decl := view «declaration» stx,
  match decl.inner with
  | declaration.inner.view.constant c@{sig := {params := bracketed_binders.view.simple [], type := type}, ..} := do
    let mdata := kvmap.set_name {} `command `constant,
    mods ← decl_modifiers_to_pexpr decl.modifiers,
    let id := ident_univ_params_to_pexpr c.name,
    type ← to_pexpr type.type,
    old_elab_command stx $ expr.mdata mdata $ expr.mk_capp `_ [mods, id, type]
  | declaration.inner.view.def_like dl := do
      let kind := match dl.kind with
      | def_like.kind.view.theorem _ := 0
      | def_like.kind.view.def _ := 1
      | def_like.kind.view.abbreviation _ := 5,
      elab_def_like stx decl.modifiers dl kind

  -- these are almost macros for `def`, except the elaborator handles them specially at a few places
  -- based on the kind
  | declaration.inner.view.example ex :=
    elab_def_like stx decl.modifiers {
      kind := def_like.kind.view.def,
      name := {id := name.anonymous},
      sig := {..ex.sig},
      ..ex} 2
  | declaration.inner.view.instance i :=
    elab_def_like stx decl.modifiers {
      kind := def_like.kind.view.def,
      name := i.name.get_or_else {id := name.anonymous},
      sig := {..i.sig},
      ..i} 3

  | declaration.inner.view.inductive ind@{«class» := none, sig := {params := bracketed_binders.view.simple bbs}, ..} := do
    let mdata := kvmap.set_name {} `command `inductives,
    mods ← decl_modifiers_to_pexpr decl.modifiers,
    attrs ← attrs_to_pexpr (match decl.modifiers.attrs with
      | some attrs := attrs.attrs
      | none       := []),
    let mut_attrs := expr.mk_capp `_ [attrs],
    match ind.old_univ_params with
    | some uparams :=
      modify_current_scope $ λ sc, {sc with univs :=
        (uparams.ids.map mangle_ident).foldl (λ m id, ordered_rbmap.insert m id (level.param id)) sc.univs}
    | none := pure (),
    let uparams := names_to_pexpr $ match ind.old_univ_params with
    | some uparams := uparams.ids.map mangle_ident
    | none := [],
    let id := mangle_ident ind.name.id,
    let type := get_opt_type ind.sig.type,
    type ← to_pexpr type,
    let ind_l := expr.local id id type binder_info.default,
    let inds := expr.mk_capp `_ [ind_l],
    params ← simple_binders_to_pexpr bbs,
    intro_rules ← ind.intro_rules.mmap (λ (r : intro_rule.view), do
      ({params := bracketed_binders.view.simple [], type := some ty}) ← pure r.sig
        | error stx "declaration.elaborate: unexpected input",
      type ← to_pexpr ty.type,
      let name := mangle_ident r.name,
      pure $ expr.local name name type binder_info.default),
    let intro_rules := expr.mk_capp `_ intro_rules,
    let intro_rules := expr.mk_capp `_ [intro_rules],
    let infer_kinds := ind.intro_rules.map $ λ (r : intro_rule.view), infer_mod_to_pexpr r.infer_mod,
    let infer_kinds := expr.mk_capp `_ infer_kinds,
    let infer_kinds := expr.mk_capp `_ [infer_kinds],
    old_elab_command stx $ expr.mdata mdata $
      expr.mk_capp `_ [mods, mut_attrs, uparams, inds, params, intro_rules, infer_kinds]

  | declaration.inner.view.structure s@{keyword := structure_kw.view.structure _, sig := {params := bracketed_binders.view.simple bbs}, ..} := do
    let mdata := kvmap.set_name {} `command `structure,
    mods ← decl_modifiers_to_pexpr decl.modifiers,
    match s.old_univ_params with
    | some uparams :=
      modify_current_scope $ λ sc, {sc with univs :=
        (uparams.ids.map mangle_ident).foldl (λ m id, ordered_rbmap.insert m id (level.param id)) sc.univs}
    | none := pure (),
    let uparams := names_to_pexpr $ match s.old_univ_params with
    | some uparams := uparams.ids.map mangle_ident
    | none := [],
    let name := mangle_ident s.name.id,
    let name := expr.local name name dummy binder_info.default,
    let type := get_opt_type s.sig.type,
    type ← to_pexpr type,
    params ← simple_binders_to_pexpr bbs,
    let parents := match s.extends with
    | some ex := ex.parents
    | none    := [],
    parents ← parents.mmap (to_pexpr ∘ sep_by.elem.view.item),
    let parents := expr.mk_capp `_ parents,
    let mk := match s.ctor with
    | some ctor := mangle_ident ctor.name
    | none      := `mk,
    let mk := expr.local mk mk dummy binder_info.default,
    let infer := infer_mod_to_pexpr (s.ctor >>= structure_ctor.view.infer_mod),
    field_blocks ← s.field_blocks.mmap (λ bl, do
      (bi, content) ← match bl with
        | structure_field_block.view.explicit {content := struct_explicit_binder_content.view.notation _} :=
          error stx "declaration.elaborate: unexpected input"
        | structure_field_block.view.explicit {content := struct_explicit_binder_content.view.other c} :=
          pure (binder_info.default, c)
        | structure_field_block.view.implicit {content := c} := pure (binder_info.implicit, c)
        | structure_field_block.view.strict_implicit {content := c} := pure (binder_info.strict_implicit, c)
        | structure_field_block.view.inst_implicit {content := c} := pure (binder_info.inst_implicit, c),
      let bi := expr.local `_ `_ dummy bi,
      let ids := names_to_pexpr $ content.ids.map mangle_ident,
      let kind := infer_mod_to_pexpr content.infer_mod,
      let type := get_opt_type content.sig.type,
      type ← to_pexpr type,
      pure $ expr.mk_capp `_ [bi, ids, kind, type]),
    let field_blocks := expr.mk_capp `_ field_blocks,
    old_elab_command stx $ expr.mdata mdata $
      expr.mk_capp `_ [mods, uparams, name, params, parents, type, mk, infer, field_blocks]
  | _ :=
    error stx "declaration.elaborate: unexpected input"

def variables.elaborate : elaborator :=
λ stx, do
  let mdata := kvmap.set_name {} `command `variables,
  let v := view «variables» stx,
  vars ← match v.binders with
  | bracketed_binders.view.simple bbs := bbs.mfilter $ λ b, do
    let (bi, id, type) := b.to_binder_info,
    if type.is_of_kind binding_annotation_update then do
      sc ← current_scope,
      let id := mangle_ident id,
      match sc.vars.find id with
      | some (_, v) :=
        modify_current_scope $ λ sc, {sc with vars :=
          sc.vars.insert id {v with binder_info := bi}}
      | none := error (syntax.ident id) "",
      pure ff
    else pure tt
  | _ := error stx "variables.elaborate: unexpected input",
  vars ← simple_binders_to_pexpr vars,
  old_elab_command stx $ expr.mdata mdata vars

def include.elaborate : elaborator :=
λ stx, do
  let v := view «include» stx,
  -- TODO(Sebastian): error checking
  modify_current_scope $ λ sc, {sc with include_vars :=
    v.ids.foldl (λ vars v, vars.insert $ mangle_ident v) sc.include_vars}

-- TODO: rbmap.remove
/-
def omit.elaborate : elaborator :=
λ stx, do
  let v := view «omit» stx,
  modify $ λ st, {st with local_state := {sc with include_vars :=
    v.ids.foldl (λ vars v, vars.remove $ mangle_ident v) sc.include_vars}}
-/

def module.header.elaborate : elaborator :=
λ stx, do
  let header := view module.header stx,
  match header with
  | {«prelude» := some _, imports := []} := pure ()
  | _ := error stx "not implemented: imports"

def prec_to_nat : option precedence.view → nat
| (some prec) := prec.term.to_nat
| none        := 0

-- TODO(Sebastian): Command parsers like `structure` will need access to these
def command_parser_config.register_notation_tokens (spec : notation_spec.view) (cfg : command_parser_config) :
  except string command_parser_config :=
do spec.rules.mfoldl (λ (cfg : command_parser_config) r, match r.symbol with
   | notation_symbol.view.quoted {symbol := some a, prec := prec, ..} :=
     pure {cfg with tokens := cfg.tokens.insert a.val.trim {«prefix» := a.val.trim, lbp := prec_to_nat prec}}
   | _ := throw "register_notation_tokens: unreachable") cfg

def command_parser_config.register_notation_parser (k : syntax_node_kind) (nota : notation.view)
  (cfg : command_parser_config) : except string command_parser_config :=
do -- build and register parser
   ps ← nota.spec.rules.mmap (λ r : rule.view, do
     psym ← match r.symbol with
     | notation_symbol.view.quoted {symbol := some a ..} :=
       pure (symbol a.val : term_parser)
     | _ := throw "register_notation_parser: unreachable",
     ptrans ← match r.transition with
     | some (transition.view.binder b) :=
       pure $ some $ term.binder_ident.parser
     | some (transition.view.binders b) :=
       pure $ some $ term.binders.parser
     | some (transition.view.arg {action := none, ..}) :=
       pure $ some term.parser
     | some (transition.view.arg {action := some {kind := action_kind.view.prec prec}, ..}) :=
       pure $ some $ term.parser prec.to_nat
     | some (transition.view.arg {action := some {kind := action_kind.view.scoped sc}, ..}) :=
       pure $ some $ term.parser $ prec_to_nat sc.prec
     | none := pure $ none
     | _ := throw "register_notation_parser: unimplemented",
     pure $ psym::ptrans.to_monad
   ),
   first_rule::_ ← pure nota.spec.rules | throw "register_notation_parser: unreachable",
   first_tk ← match first_rule.symbol with
   | notation_symbol.view.quoted {symbol := some a ..} :=
     pure a.val.trim
   | _ := throw "register_notation_parser: unreachable",
   let ps := ps.bind id,
   cfg ← match nota.local, nota.spec.prefix_arg with
   | none,   none   := pure {cfg with leading_term_parsers :=
     cfg.leading_term_parsers.insert first_tk $ parser.combinators.node k ps}
   | some _, none   := pure {cfg with local_leading_term_parsers :=
     cfg.local_leading_term_parsers.insert first_tk $ parser.combinators.node k ps}
   | none,   some _ := pure {cfg with trailing_term_parsers :=
     cfg.trailing_term_parsers.insert first_tk $ parser.combinators.node k (get_leading::ps.map coe)}
   | some _, some _ := pure {cfg with local_trailing_term_parsers :=
     cfg.local_trailing_term_parsers.insert first_tk $ parser.combinators.node k (get_leading::ps.map coe)},
   pure cfg

/-- Recreate `elaborator_state.parser_cfg` from the elaborator state and the initial config,
    effectively treating it as a cache. -/
def update_parser_config : elaborator_m unit :=
do st ← get,
   sc ← current_scope,
   cfg ← read,
   let ccfg := cfg.initial_parser_cfg.to_command_parser_config,
   ccfg ← st.reserved_notations.mfoldl (λ ccfg rnota,
     match command_parser_config.register_notation_tokens rnota.spec ccfg with
     | except.ok ccfg := pure ccfg
     | except.error e := error (review reserve_notation rnota) e) ccfg,
   ccfg ← (st.notations ++ sc.notations).mfoldl (λ ccfg nota,
     match command_parser_config.register_notation_tokens nota.nota.spec ccfg >>=
               command_parser_config.register_notation_parser nota.kind nota.nota with
     | except.ok ccfg := pure ccfg
     | except.error e := error (review «notation» nota.nota) e) ccfg,
   put {st with parser_cfg := {cfg.initial_parser_cfg with to_command_parser_config := ccfg}}

def postprocess_notation_spec (spec : notation_spec.view) : notation_spec.view :=
-- default leading tokens to `max`
-- NOTE: should happen after copying precedences from reserved notation
match spec with
| {prefix_arg := none, rules := r@{symbol := notation_symbol.view.quoted sym@{prec := none, ..}, ..}::rs} :=
  {spec with rules := {r with symbol := notation_symbol.view.quoted {sym with prec := some
    {term := precedence_term.view.lit $ precedence_lit.view.num $ number.view.of_nat max_prec}
  }}::rs}
| _ := spec

def reserve_notation.elaborate : elaborator :=
λ stx, do
  let v := view reserve_notation stx,
  let v := {v with spec := postprocess_notation_spec v.spec},
  -- TODO: sanity checks?
  modify $ λ st, {st with reserved_notations := v::st.reserved_notations},
  update_parser_config

def match_precedence : option precedence.view → option precedence.view → bool
| none      (some rp) := tt
| (some sp) (some rp) := sp.term.to_nat = rp.term.to_nat
| _         _         := ff

/-- Check if a notation is compatible with a reserved notation, and if so, copy missing
    precedences in the notation from the reserved notation. -/
def match_spec (spec reserved : notation_spec.view) : option notation_spec.view :=
do guard $ spec.prefix_arg.is_some = reserved.prefix_arg.is_some,
   rules ← (spec.rules.zip reserved.rules).mmap $ λ ⟨sr, rr⟩, do {
     notation_symbol.view.quoted sq@{symbol := some sa, ..} ← pure sr.symbol
       | failure,
     notation_symbol.view.quoted rq@{symbol := some ra, ..} ← pure rr.symbol
       | failure,
     guard $ sa.val.trim = ra.val.trim,
     guard $ match_precedence sq.prec rq.prec,
     st ← match sr.transition, rr.transition with
     | some (transition.view.binder sb), some (transition.view.binder rb) :=
       guard (match_precedence sb.prec rb.prec) *> pure rr.transition
     | some (transition.view.binders sb), some (transition.view.binders rb) :=
       guard (match_precedence sb.prec rb.prec) *> pure rr.transition
     | some (transition.view.arg sarg), some (transition.view.arg rarg) := do
       sact ← match action.view.kind <$> sarg.action, action.view.kind <$> rarg.action with
       | some (action_kind.view.prec sp), some (action_kind.view.prec rp) :=
         guard (sp.to_nat = rp.to_nat) *> pure sarg.action
       | none,                            some (action_kind.view.prec rp) :=
         pure rarg.action
       | _, _ := failure,
       pure $ some $ transition.view.arg {sarg with action := sact}
     | none,    none    := pure none
     | _,       _       := failure,
     pure $ {rule.view .
       symbol := notation_symbol.view.quoted rq,
       transition := st}
   },
   pure $ {spec with rules := rules}

def notation.elaborate_aux : notation.view → elaborator_m notation.view :=
λ nota, do
  st ← get,
  -- check reserved notations
  matched ← pure $ st.reserved_notations.filter_map $
    λ rnota, match_spec nota.spec rnota.spec,
  nota ← match matched with
  | [matched] := pure {nota with spec := matched}
  | []        := pure nota
  | _         := error (review «notation» nota) "invalid notation, matches multiple reserved notations",
  -- TODO: sanity checks
  pure {nota with spec := postprocess_notation_spec nota.spec}

-- TODO(Sebastian): better kind names, module prefix?
def mk_notation_kind : elaborator_m syntax_node_kind :=
do st ← get,
   put {st with notation_counter := st.notation_counter + 1},
   pure {name := (`_notation).mk_numeral st.notation_counter}

/-- Register a notation in the expander. Unlike with notation parsers, there is no harm in
    keeping local notation macros registered after closing a section. -/
def register_notation_macro (nota : notation.view) : elaborator_m notation_macro :=
do k ← mk_notation_kind,
   let m : notation_macro := ⟨k, nota⟩,
   let transf := mk_notation_transformer m,
   modify $ λ st, {st with expander_cfg := {st.expander_cfg with transformers := st.expander_cfg.transformers.insert k.name transf}},
   pure m

def notation.elaborate : elaborator :=
λ stx, do
  let nota := view «notation» stx,
  -- HACK: ignore list literal notation using :fold
  let uses_fold := nota.spec.rules.any $ λ r, match r.transition with
    | some (transition.view.arg {action := some {kind := action_kind.view.fold _, ..}, ..}) := tt
    | _ := ff,
  if uses_fold then do {
    cfg ← read,
    modify $ λ st, {st with messages := st.messages.add {filename := cfg.filename, pos := ⟨1,0⟩,
      severity := message_severity.warning, text := "ignoring notation using 'fold' action"}}
  } else do {
    nota ← notation.elaborate_aux nota,
    m ← register_notation_macro nota,
    match nota.local with
      | some _ := modify_current_scope $ λ sc, {sc with notations := m::sc.notations}
      | none   := modify $ λ st, {st with notations := m::st.notations},
    update_parser_config
  }

def universe.elaborate : elaborator :=
λ stx, do
  let univ := view «universe» stx,
  let id := mangle_ident univ.id,
  sc ← current_scope,
  match sc.univs.find id with
  | none   := modify_current_scope $ λ sc, {sc with univs := sc.univs.insert id (level.param id)}
  | some _ := error stx $ "a universe named '" ++ to_string id ++ "' has already been declared in this scope"

def attribute.elaborate : elaborator :=
λ stx, do
  let attr := view «attribute» stx,
  let mdata := kvmap.set_name {} `command `attribute,
  let mdata := mdata.set_bool `local $ attr.local.is_some,
  attrs ← attrs_to_pexpr attr.attrs,
  ids ← attr.ids.mmap (λ id, match id.preresolved with
    | []  := error (syntax.ident id) $ "unknown identifier '" ++ to_string id.val ++ "'"
    | [c] := pure $ expr.const c []
    | _   := error (syntax.ident id) "invalid 'attribute' command, identifier is ambiguous"),
  let ids := expr.mk_capp `_ ids,
  old_elab_command stx $ expr.mdata mdata $ expr.app attrs ids

def check.elaborate : elaborator :=
λ stx, do
  let v := view check stx,
  let mdata := kvmap.set_name {} `command `#check,
  e ← to_pexpr v.term,
  old_elab_command stx $ expr.mdata mdata e

def open.elaborate : elaborator :=
λ stx, do
  let v := view «open» stx,
  -- TODO: do eager sanity checks (namespace does not exist, etc.)
  modify_current_scope $ λ sc, {sc with open_decls := sc.open_decls ++ v.spec}

def export.elaborate : elaborator :=
λ stx, do
  let v := view «export» stx,
  ns ← get_namespace,
  -- TODO: do eager sanity checks (namespace does not exist, etc.)
  modify $ λ st, {st with export_decls := st.export_decls ++ v.spec.map (λ spec, ⟨ns, spec⟩)}

def init_quot.elaborate : elaborator :=
λ stx, old_elab_command stx $ expr.mdata (kvmap.set_name {} `command `init_quot) dummy

def set_option.elaborate : elaborator :=
λ stx, do
  let v := view «set_option» stx,
  let opt := v.opt.val,
  sc ← current_scope,
  let opts := sc.options,
  -- TODO(Sebastian): check registered options
  let opts := match v.val with
  | option_value.view.bool b := opts.set_bool opt (match b with bool_option_value.view.true _ := tt | _ := ff)
  | option_value.view.string lit := (match lit.value with
    | some s := opts.set_string opt s
    | none   := opts)  -- parser already failed
  | option_value.view.num lit := opts.set_nat opt lit.to_nat,
  modify_current_scope $ λ sc, {sc with options := opts}

/-- List of commands: recursively elaborate each command. -/
def no_kind.elaborate : elaborator := λ stx, do
  some n ← pure stx.as_node
    | error stx "no_kind.elaborate: unreachable",
  n.args.mmap' command.elaborate

def end.elaborate : elaborator :=
λ cmd, do
  let v := view «end» cmd,
  st ← get,
  -- NOTE: bottom-most (module) scope cannot be closed
  sc::sc'::scps ← pure st.scopes
    | error cmd "invalid 'end', there is no open scope to end",
  let end_name := mangle_ident $ v.name.get_or_else name.anonymous,
  when (end_name ≠ sc.header) $
    error cmd $ "invalid end of " ++ sc.cmd ++ ", expected name '" ++
      to_string sc.header ++ "'",
  put {st with scopes := sc'::scps},
  -- local notations may have vanished
  update_parser_config

def section.elaborate : elaborator :=
λ cmd, do
  let sec := view «section» cmd,
  let header := mangle_ident $ sec.name.get_or_else name.anonymous,
  sc ← current_scope,
  modify $ λ st, {st with scopes := {sc with cmd := "section", header := header}::st.scopes}

def namespace.elaborate : elaborator :=
λ cmd, do
  let v := view «namespace» cmd,
  let header := mangle_ident v.name,
  sc ← current_scope,
  ns ← get_namespace,
  let sc' := {sc with cmd := "namespace", header := header, ns_stack := (ns ++ header)::sc.ns_stack},
  modify $ λ st, {st with scopes := sc'::st.scopes}

def eoi.elaborate : elaborator :=
λ cmd, do
  st ← get,
  when (st.scopes.length > 1) $
    error cmd "invalid end of input, expected 'end'"

-- TODO(Sebastian): replace with attribute
def elaborators : rbmap name elaborator (<) := rbmap.from_list [
  (module.header.name, module.header.elaborate),
  (notation.name, notation.elaborate),
  (reserve_notation.name, reserve_notation.elaborate),
  (universe.name, universe.elaborate),
  (no_kind.name, no_kind.elaborate),
  (end.name, end.elaborate),
  (section.name, section.elaborate),
  (namespace.name, namespace.elaborate),
  (variables.name, variables.elaborate),
  (include.name, include.elaborate),
  --(omit.name, omit.elaborate),
  (declaration.name, declaration.elaborate),
  (attribute.name, attribute.elaborate),
  (open.name, open.elaborate),
  (export.name, export.elaborate),
  (check.name, check.elaborate),
  (init_quot.name, init_quot.elaborate),
  (set_option.name, set_option.elaborate),
  (module.eoi.name, eoi.elaborate)
] _

-- TODO: optimize
def is_open_namespace (sc : scope) : name → bool
| name.anonymous := tt
| ns :=
  -- check surrounding namespaces
  ns ∈ sc.ns_stack ∨
  -- check opened namespaces
  sc.open_decls.any (λ od, od.id.val = ns) ∨
  -- TODO: check active exports
  ff

-- TODO: `hiding`, `as`, `renaming`
def match_open_spec (n : name) (spec : open_spec.view) : option name :=
let matches_only := match spec.only with
| none := tt
| some only := n = only.id.val ∨ only.ids.any (λ id, n = id.val) in
if matches_only then some (spec.id.val ++ n) else none

def resolve_context : name → elaborator_m (list name)
| n := do
  st ← get,
  sc ← current_scope, pure $

  -- TODO(Sebastian): check the interaction betwen preresolution and section variables
  match sc.vars.find n with
  | some (_, v) := [v.uniq_name]
  | _ :=

  -- global resolution

  -- check surrounding namespaces first
  -- TODO: check for `protected`
  match sc.ns_stack.filter (λ ns, st.env.contains (ns ++ n)) with
  | ns::_ := [ns ++ n] -- prefer innermost namespace
  | _ :=

  -- check environment directly
  (let unrooted := n.replace_prefix `_root_ name.anonymous in
   match st.env.contains unrooted with
   | tt := [unrooted]
   | _ := [])
  ++
  -- check opened namespaces
  (let ns' := sc.open_decls.filter_map (match_open_spec n) in
   ns'.filter (λ n', st.env.contains n'))
  ++
  -- check active exports
  -- TODO: optimize
  -- TODO: Lean 3 activates an export in `foo` even on `open foo (specific_thing)`, but does that make sense?
  (let eds' := st.export_decls.filter (λ ed, is_open_namespace sc ed.in_ns) in
   let ns' := eds'.filter_map (λ ed, match_open_spec n ed.spec) in
   ns'.filter (λ n', st.env.contains n'))

  -- TODO: projection notation

def preresolve : syntax → elaborator_m syntax
| (syntax.ident id) := do
  let n := mangle_ident id,
  ns ← resolve_context n,
  pure $ syntax.ident {id with preresolved := ns ++ id.preresolved}
| (syntax.raw_node n) := do
  args ← n.args.mmap preresolve,
  pure $ syntax.raw_node {n with args := args}
| stx := pure stx

def mk_state (cfg : elaborator_config) (opts : options) : elaborator_state := {
  parser_cfg := cfg.initial_parser_cfg,
  expander_cfg := {transformers := expander.builtin_transformers, ..cfg},
  ngen := ⟨`_ngen.fixme, 0⟩,
  scopes := [{cmd := "MODULE", header := `MODULE, options := opts}]}

def process_command (cfg : elaborator_config) (st : elaborator_state) (cmd : syntax) : elaborator_state :=
let st := {st with messages := message_log.empty} in
let r := @except_t.run _ id _ $ flip state_t.run st $ flip reader_t.run cfg $ rec_t.run
  (command.elaborate cmd)
  (λ _, error cmd "elaborator.run: recursion depth exceeded")
  (λ cmd, do
    some n ← pure cmd.as_node |
      error cmd $ "not a command: " ++ to_string cmd,
    some elab ← pure $ elaborators.find n.kind.name |
      error cmd $ "unknown command: " ++ to_string n.kind.name,
    cmd' ← preresolve cmd,
    elab cmd') in
match r with
| except.ok ((), st) := st
| except.error e     := {st with messages := st.messages.add e}

end elaborator
end lean
