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
constant environment.empty : environment

namespace elaborator
-- TODO(Sebastian): move
-- TODO(Sebastian): should be its own monad?
structure name_generator :=
(«prefix» : name)
(next_idx : nat) -- TODO(Sebastian): uint32

/-- Simplified state of the Lean 3 parser. Maps are replaced with lists for easier interop. -/
structure old_elaborator_state :=
(env : environment)
(ngen : name_generator)
(univs : list (name × level))
(vars : list (name × expr))
(include_vars : list name)
(options : options)
(next_inst_idx : nat)

constant elaborate_command (filename : string) : expr → old_elaborator_state →
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

structure local_state :=
(notations : list notation_macro := [])
/- The set of local universe variables.
   We remember their insertion order so that we can keep the order when copying them to declarations. -/
(univs : ordered_rbmap name level (<) := ordered_rbmap.empty)
/- The set of local variables. -/
(vars : ordered_rbmap name expr  (<) := ordered_rbmap.empty)
/- The subset of `vars` that is tagged as always included. -/
(include_vars : rbtree name (<) := mk_rbtree _ _)

structure elaborator_state :=
-- TODO(Sebastian): retrieve from environment
(reserved_notations : list reserve_notation.view := [])
(notations : list notation_macro := [])
(notation_counter := 0)

(local_state : local_state := {})
(messages : message_log := message_log.empty)
(parser_cfg : module_parser_config)
(expander_cfg : expander.expander_config)
(env : environment := environment.empty)
(ngen : name_generator)
(options : options)
(next_inst_idx : nat := 0)

@[derive monad monad_reader monad_state monad_except]
def elaborator_t (m : Type → Type) [monad m] := reader_t elaborator_config $ state_t elaborator_state $ except_t message m
abbreviation elaborator_m := elaborator_t id
abbreviation elaborator := reader_t syntax elaborator_m unit
/-- An elaborator in a coroutine. Can accept and process multiple commands asynchronously
    (e.g. `section`) -/
abbreviation coelaborator_m := rec_t unit unit $ elaborator_t $ coroutine syntax elaborator_state
abbreviation coelaborator := coelaborator_m unit

/-- Recursively elaborate any command. -/
def command.elaborate : coelaborator := recurse ()

section
local attribute [reducible] elaborator_t
attribute [derive monad_coroutine] coelaborator_m
instance elaborator_t.monad_reader_adapter (m : Type → Type) [monad m] :
  monad_reader_adapter elaborator_config elaborator_config (elaborator_t m) (elaborator_t m) :=
infer_instance
def current_command : coelaborator_m syntax :=
monad_lift (coroutine.read : coroutine syntax elaborator_state _)
def with_current_command {α : Type} (cmd : syntax) : coelaborator_m α → coelaborator_m α :=
monad_map (λ β, (coroutine.adapt (λ _, cmd) : coroutine syntax elaborator_state β → coroutine syntax elaborator_state β))
end

instance elaborator_m_coe_coelaborator_m {α : Type} : has_coe (elaborator_m α) (coelaborator_m α) :=
⟨λ x rec cfg st, except_t.mk $ pure $ x cfg st⟩

instance elaborator_coe_coelaborator : has_coe elaborator coelaborator :=
⟨λ x, do stx ← current_command, x stx⟩

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
  st ← get,
  match fn.kind with
  | some level.leading := (match view level.leading stx, args with
    | level.leading.view.hole _, [] := pure $ level.mvar name.anonymous
    | level.leading.view.lit lit, [] := pure $ level.of_nat lit.to_nat
    | level.leading.view.var id, [] := let id := mangle_ident id in (match st.local_state.univs.find id with
      | some _ := pure $ level.param id
      | none   := error stx $ "unknown universe variable '" ++ to_string id ++ "'")
    | level.leading.view.max _, (arg::args) := list.foldl level.max <$> to_level arg <*> args.mmap to_level
    | level.leading.view.imax _, (arg::args) := list.foldl level.imax <$> to_level arg <*> args.mmap to_level
    | _, _ := error stx "ill-formed universe level")
  | some level.trailing := (match view level.trailing stx, args with
    | level.trailing.view.add_lit lta, [] := do
      l ← to_level lta.lhs,
      pure $ level_add l lta.rhs.to_nat
    | _, _ := error stx "ill-formed universe level")
  | _ := error stx $ "to_level: unexpected input: " ++ to_string stx

def expr.mk_annotation (ann : name) (e : expr) :=
expr.mdata (kvmap.set_name {} `annotation `anonymous_constructor) e

def dummy : expr := expr.const `Prop []

def to_pexpr : syntax → elaborator_m expr
| (syntax.ident id)   := pure $ expr.const (mangle_ident id) []
| stx@(syntax.raw_node {kind := k, args := args}) := (match k with
  | @ident_univs := (match view ident_univs stx with
    | {id := id, univs := some univs} := expr.const (mangle_ident id) <$> univs.levels.mmap to_level
    | {id := id, univs := none}       := pure $ expr.const (mangle_ident id) [])
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
    lam ← expr.lam id binder_info.default <$> to_pexpr v.prop <*> to_pexpr proof,
    pure $ expr.mk_annotation `have lam
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
    | explicit_modifier.view.explicit _         := `explicit
    | explicit_modifier.view.partial_explicit _ := `partial_explicit,
    expr.mk_annotation ann <$> to_pexpr (review ident_univs v.id)
  | @number := do
    let v := view number stx,
    pure $ expr.lit $ literal.nat_val v.to_nat
  | @choice := do
    last::rev ← list.reverse <$> args.mmap (λ a, to_pexpr a)
      | error stx "ill-formed choice",
    pure $ expr.mk_annotation `choice $
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

    let m := kvmap.set_nat {} `structure_instance fields.length,
    let m := kvmap.set_bool m `catchall catchall,
    let m := kvmap.set_name m `struct $
      (mangle_ident <$> struct_inst_type.view.id <$> v.type).get_or_else name.anonymous,
    let dummy := expr.sort level.zero,
    pure $ expr.mdata m $ (fields ++ sources).foldr expr.app dummy
  | @«match» := do
    let v := view «match» stx,
    let fn_name := `_match_fn,
    fn ← expr.lam fn_name -- TODO: unhygienic
      binder_info.default
      <$> to_pexpr (get_opt_type v.type),
    eqns ← match v.equations with
    | [] := pure [fn $ expr.mdata (kvmap.set_bool {} `no_equation ff) dummy]
    | eqns := (eqns.map sep_by.elem.view.item).mmap $ λ (eqn : match_equation.view), do {
      lhs ← eqn.lhs.mmap $ λ l, to_pexpr l.item,
      let lhs := lhs.foldl expr.app (expr.fvar fn_name),
      rhs ← to_pexpr eqn.rhs,
      pure $ fn $ expr.mdata (kvmap.set_bool {} `equation tt) $ expr.app lhs rhs
    },
    some eqns ← pure $ eqns.foldr1_opt expr.app
      | error stx "to_pexpr: unreachable",
    pure $ expr.mdata (kvmap.set_bool {} `pre_equations tt) eqns
  | _ := error stx $ "unexpected node: " ++ to_string k.name)
| stx := error stx $ "unexpected: " ++ to_string stx

def old_elab_command (stx : syntax) (cmd : expr) : elaborator_m unit :=
do cfg ← read,
   st ← get,
   let (st', msgs) := elaborate_command cfg.filename cmd {
     univs := st.local_state.univs.entries,
     vars := st.local_state.vars.entries,
     include_vars := st.local_state.include_vars.to_list,
     ..st},
   match st' with
   | some st' := put {
     local_state := {st.local_state with
       univs := ordered_rbmap.of_list st'.univs,
       vars := ordered_rbmap.of_list st'.vars,
       include_vars := rbtree.of_list st'.include_vars,
     },
     ..st', ..st}
   | none := pure (),  -- error
   modify $ λ st, {st with messages := st.messages ++ msgs}

def attrs_to_pexpr (attrs : list (sep_by.elem.view attr_instance.view (option syntax_atom))) : elaborator_m expr :=
expr.mk_capp `_ <$> attrs.mmap (λ attr,
  expr.mk_capp (mangle_ident attr.item.name) <$> attr.item.args.mmap to_pexpr)

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

/-- Execute `elab` and reset local state (universes, ...) after it has finished. -/
@[specialize] def locally {m : Type → Type} [monad m] [monad_state elaborator_state m] (elab : m unit) :
  m unit := do
  local_st ← elaborator_state.local_state <$> get,
  elab,
  modify $ λ st, {st with local_state := local_st}

def declaration.elaborate : elaborator :=
locally $ λ stx, do
  let decl := view «declaration» stx,
  match decl.inner with
  | declaration.inner.view.constant c@{sig := {params := bracketed_binders.view.simple [], type := type}, ..} := do
    let mdata := kvmap.set_name {} `command `constant,
    mods ← decl_modifiers_to_pexpr decl.modifiers,
    let id := ident_univ_params_to_pexpr c.name,
    type ← to_pexpr type.type,
    old_elab_command stx $ expr.mdata mdata $ expr.mk_capp `_ [mods, id, type]
  | declaration.inner.view.constant _ :=
    error stx "declration.elaborate: unexpected input"
  -- just test `to_pexpr` for now
  | declaration.inner.view.def_like dl@{
    val := decl_val.view.simple val,
    sig := {params := bracketed_binders.view.simple bbs}, ..} := do
    match dl.old_univ_params with
    | some uparams :=
      modify $ λ st, {st with local_state := {st.local_state with univs :=
        (uparams.ids.map mangle_ident).foldl (λ m id, ordered_rbmap.insert m id (level.param id)) st.local_state.univs}}
    | none := pure (),
    let type := get_opt_type dl.sig.type,
    let type := bbs.foldr (λ bnder type, review pi {op := syntax.atom {val := "Π"}, binders := bnder, range := type}) type,
    to_pexpr type,
    to_pexpr val.body,
    pure ()
  | _ := pure ()

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

def command_parser_config.register_notation_parser (k : syntax_node_kind) (spec : notation_spec.view)
  (cfg : command_parser_config) : except string command_parser_config :=
do -- build and register parser
   ps ← spec.rules.mmap (λ r : rule.view, do
     psym ← match r.symbol with
     | notation_symbol.view.quoted {symbol := some a ..} :=
       pure (symbol a.val : term_parser)
     | _ := throw "register_notation_parser: unreachable",
     ptrans ← match r.transition with
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
   first_rule::_ ← pure spec.rules | throw "register_notation_parser: unreachable",
   first_tk ← match first_rule.symbol with
   | notation_symbol.view.quoted {symbol := some a ..} :=
     pure a.val.trim
   | _ := throw "register_notation_parser: unreachable",
   let ps := ps.bind id,
   cfg ← match spec.prefix_arg with
   | none   := pure {cfg with leading_term_parsers :=
     cfg.leading_term_parsers.insert first_tk $ parser.combinators.node k ps}
   | some _ := pure {cfg with trailing_term_parsers :=
     cfg.trailing_term_parsers.insert first_tk $ parser.combinators.node k (read::ps.map coe)},
   pure cfg

/-- Recreate `elaborator_state.parser_cfg` from the elaborator state and the initial config,
    effectively treating it as a cache. -/
def update_parser_config : elaborator_m unit :=
do st ← get,
   cfg ← read,
   let ccfg := cfg.initial_parser_cfg.to_command_parser_config,
   ccfg ← st.reserved_notations.mfoldl (λ ccfg rnota,
     match command_parser_config.register_notation_tokens rnota.spec ccfg with
     | except.ok ccfg := pure ccfg
     | except.error e := error (review reserve_notation rnota) e) ccfg,
   ccfg ← (st.notations ++ st.local_state.notations).mfoldl (λ ccfg nota,
     match command_parser_config.register_notation_tokens nota.nota.spec ccfg >>=
               command_parser_config.register_notation_parser nota.kind nota.nota.spec with
     | except.ok ccfg := pure ccfg
     | except.error e := error (review «notation» nota.nota) e) ccfg,
   put {st with parser_cfg := {cfg.initial_parser_cfg with to_command_parser_config := ccfg}}

def yield_to_outside : coelaborator_m unit :=
do st ← get,
   yield st,
   -- reset messages for next command
   put {st with messages := message_log.empty}

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
    modify $ λ st, match nota.local with
      | some _ := {st with local_state := {st.local_state with notations := m::st.local_state.notations}}
      | none   := {st with notations := m::st.notations},
    update_parser_config
  }

def universe.elaborate : elaborator :=
λ stx, do
  let univ := view «universe» stx,
  let id := mangle_ident univ.id,
  st ← get,
  match st.local_state.univs.find id with
  | none   := put {st with local_state := {st.local_state with univs := st.local_state.univs.insert id (level.param id)}}
  | some _ := error stx $ "a universe named '" ++ to_string id ++ "' has already been declared in this scope"

def attribute.elaborate : elaborator :=
λ stx, do
  let attr := view «attribute» stx,
  let mdata := kvmap.set_name {} `command `attribute,
  let mdata := mdata.set_bool `local $ attr.local.is_some,
  attrs ← attrs_to_pexpr attr.attrs,
  let ids := expr.mk_capp `_ $ attr.ids.map $ λ id, expr.const (mangle_ident id) [],
  old_elab_command stx $ expr.mdata mdata $ expr.app attrs ids

/-- List of commands: recursively elaborate each command. -/
def no_kind.elaborate : coelaborator := do
  stx ← current_command,
  some n ← pure stx.as_node
    | error stx "no_kind.elaborate: unreachable",
  n.args.mmap' (λ cmd, with_current_command cmd command.elaborate)

def commands.elaborate (stop_on_end_cmd : bool) : ℕ → coelaborator
| 0 := do cmd ← current_command, error cmd "commands.elaborate: out of fuel"
| (n+1) := do
  cmd ← current_command,
  let elab_and_recurse : coelaborator := do {
    command.elaborate,
    yield_to_outside,
    commands.elaborate n
  },
  match syntax_node.kind <$> cmd.as_node with
  | @«end» :=
    if stop_on_end_cmd then
      pure ()
    else
      -- TODO(Sebastian): should recover
      error cmd "invalid 'end', there is no open scope to end"
  | module.eoi :=
    if stop_on_end_cmd then
      error cmd "invalid end of input, expected 'end'"
    else
      pure ()
  | _ := elab_and_recurse

def elab_scope (cmd_name : string) (exp_end_name : option name) : coelaborator :=
do locally $ do {
     yield_to_outside,
     commands.elaborate tt 1000
   },
   -- local notations may have vanished
   update_parser_config,
   end_cmd ← view «end» <$> current_command,
   let end_name := mangle_ident <$> end_cmd.name,
   when (end_name ≠ exp_end_name) $
     error (review «end» end_cmd) $ "invalid end of " ++ cmd_name ++ ", expected name '" ++
       to_string (exp_end_name.get_or_else name.anonymous) ++ "'"

def section.elaborate : coelaborator :=
do sec ← view «section» <$> current_command,
   elab_scope "section" $ mangle_ident <$> sec.name

def namespace.elaborate : coelaborator :=
do ns ← view «namespace» <$> current_command,
   elab_scope "namespace" ns.name.val

-- TODO(Sebastian): replace with attribute
def elaborators : rbmap name coelaborator (<) := rbmap.from_list [
  (module.header.name, module.header.elaborate),
  (notation.name, notation.elaborate),
  (reserve_notation.name, reserve_notation.elaborate),
  (universe.name, universe.elaborate),
  (no_kind.name, no_kind.elaborate),
  (section.name, section.elaborate),
  (namespace.name, namespace.elaborate),
  (declaration.name, declaration.elaborate),
  (attribute.name, attribute.elaborate)
] _

protected def max_recursion := 100
protected def max_commands := 10000

protected def run (cfg : elaborator_config) : coroutine syntax elaborator_state message_log :=
do
  let st := {elaborator_state .
    parser_cfg := cfg.initial_parser_cfg,
    expander_cfg := {transformers := expander.builtin_transformers, ..cfg},
    ngen := ⟨`fixme, 0⟩,
    options := options.mk},
  p ← except_t.run $ flip state_t.run st $ flip reader_t.run cfg $ rec_t.run
    (commands.elaborate ff elaborator.max_commands)
    (λ _, modify $ λ st, {st with messages := st.messages.add {filename := "foo", pos := ⟨1,0⟩, text := "elaborator.run: out of fuel"}})
    (λ _, do
      cmd ← current_command,
      some n ← pure cmd.as_node |
        error cmd $ "not a command: " ++ to_string cmd,
      catch
        (do some elab ← pure $ elaborators.find n.kind.name |
              error cmd $ "unknown command: " ++ to_string n.kind.name,
            elab)
        (λ e, modify $ λ st, {st with messages := st.messages.add e}))
    elaborator.max_recursion,
  match p with
  | except.ok ((), st) := pure st.messages
  | except.error e     := pure $ message_log.empty.add e

end elaborator
end lean
