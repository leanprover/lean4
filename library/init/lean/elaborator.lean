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

namespace lean
namespace elaborator
open parser
open parser.term
open parser.command
open parser.command.notation_spec

structure elaborator_config :=
(filename : string)
(local_notations : list notation.view := [])
(initial_parser_cfg : module_parser_config)

structure elaborator_state :=
-- TODO(Sebastian): retrieve from environment
(reserved_notations : list reserve_notation.view := [])
-- TODO(Sebastian): retrieve from environment
(nonlocal_notations : list notation.view := [])
(messages : message_log := message_log.empty)
(parser_cfg : module_parser_config)

@[derive monad monad_reader monad_state monad_except]
def elaborator_t (m : Type → Type) [monad m] := reader_t elaborator_config $ state_t elaborator_state $ except_t message m
abbreviation elaborator_m := elaborator_t id
abbreviation elaborator := syntax → elaborator_m unit
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
def current_command : coelaborator_m syntax := monad_lift (coroutine.read : coroutine syntax elaborator_state _)
end

instance elaborator_m_coe_coelaborator_m {α : Type} : has_coe (elaborator_m α) (coelaborator_m α) :=
⟨λ x rec cfg st, except_t.mk $ pure $ x cfg st⟩

instance elaborator_coe_coelaborator : has_coe elaborator coelaborator :=
⟨λ x, do stx ← current_command, x stx⟩

def error {α : Type} (context : syntax) (text : string) : elaborator_m α :=
do cfg ← read,
   -- TODO(Sebastian): convert position
   throw {filename := cfg.filename, pos := /-context.get_pos.get_or_else-/ ⟨1,0⟩, text := text}

local attribute [instance] name.has_lt_quick

def mangle_ident (id : syntax_ident) : name :=
id.scopes.foldl name.mk_numeral id.val

def to_level : syntax → elaborator_m level
| stx := do
  some k ← pure stx.kind | error stx $ "unexpected atom: " ++ to_string stx,
  match k with
  | level.leading := (match view level.leading stx with
    | level.leading.view.hole _ := pure $ level.mvar "u"  -- TODO(Sebastian): name?
    | level.leading.view.lit lit := pure $ level.of_nat lit.to_nat
    | level.leading.view.var id := pure $ level.param $ mangle_ident id
    | _ := error stx "ill-formed universe level")
  | _ := error stx $ "unexpected node: " ++ to_string k.name

def expr.mk_annotation (ann : name) (e : expr) :=
expr.mdata (kvmap.set_name {} `annotation `anonymous_constructor) e

def to_pexpr : syntax → elaborator_m expr
| (syntax.ident id)   := pure $ expr.const (mangle_ident id) []
| stx@(syntax.raw_node {kind := k, ..}) := (match k with
  | @ident_univs := (match view ident_univs stx with
    | {id := id, univs := some univs} := expr.const (mangle_ident id) <$> univs.levels.mmap to_level
    | {id := id, univs := none}       := pure $ expr.const (mangle_ident id) [])
  | @app   := let v := view app stx in
    expr.app <$> to_pexpr v.fn <*> to_pexpr v.arg
  | @lambda := do
    let lam := view lambda stx,
    binders'.view.simple bnder ← pure lam.binders
      | error stx "ill-formed lambda",
    (bi, id, type) ← pure bnder.to_binder_info,
    expr.lam (mangle_ident id) bi <$> to_pexpr type <*> to_pexpr lam.body
  | @pi := do
    let v := view pi stx,
    binders'.view.simple bnder ← pure v.binders
      | error stx "ill-formed pi",
    (bi, id, type) ← pure bnder.to_binder_info,
    expr.pi (mangle_ident id) bi <$> to_pexpr type <*> to_pexpr v.range
  | @sort := (match view sort stx with
    | sort.view.Sort _ := pure $ expr.sort level.zero
    | sort.view.Type _ := pure $ expr.sort $ level.succ level.zero)
  | @anonymous_constructor := do
    let v := view anonymous_constructor stx,
    p ← to_pexpr $ mk_app' (review hole {}) (v.args.map prod.fst),
    pure $ expr.mk_annotation `anonymous_constructor p
  | @hole := pure $ expr.const "_" []  -- TODO
  | @«have» := do
    let v := view «have» stx,
    let id := (mangle_ident <$> opt_ident.view.id <$> v.id).get_or_else `this,
    let proof := match v.proof with
    | have_proof.view.term hpt := hpt.term
    | have_proof.view.from hpf := hpf.from.proof,
    lam ← expr.lam id binder_info.default <$> to_pexpr v.prop <*> to_pexpr proof,
    pure $ expr.mk_annotation `have lam
  | @projection := do
    let v := view projection stx,
    let val := match v.proj with
    | projection_spec.view.id id := data_value.of_name id.val
    | projection_spec.view.num n := data_value.of_nat n.to_nat,
    expr.mdata (kvmap.insert {} `field_notation val) <$> to_pexpr v.term
  | _ := error stx $ "unexpected node: " ++ to_string k.name)
| stx := error stx $ "unexpected: " ++ to_string stx

def declaration.elaborate : elaborator :=
λ stx, do
  let decl := view «declaration» stx,
  -- just test `to_pexpr` for now
  match decl.inner with
  | declaration.inner.view.def_like {val := decl_val.view.simple val, ..} :=
    to_pexpr val.body *> pure ()
  | _ := pure ()

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

def command_parser_config.register_notation_parser (spec : notation_spec.view) (cfg : command_parser_config) :
  except string command_parser_config :=
do -- build and register parser
   let k : syntax_node_kind := {name := "notation<TODO>"},
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
   ccfg ← (st.nonlocal_notations ++ cfg.local_notations).mfoldl (λ ccfg nota,
     match command_parser_config.register_notation_tokens nota.spec ccfg >>=
               command_parser_config.register_notation_parser nota.spec with
     | except.ok ccfg := pure ccfg
     | except.error e := error (review «notation» nota) e) ccfg,
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

def notation.elaborate : elaborator :=
λ stx, do
  let nota := view «notation» stx,
  when nota.local.is_some $
    error stx "notation.elaborate: unexpected local notation",
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
    modify $ λ st, {st with nonlocal_notations := nota::st.nonlocal_notations},
    update_parser_config
  }

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
  | @«notation» := do
    let nota := view «notation» cmd,
    if nota.local.is_some then do {
      nota ← notation.elaborate_aux nota,
      -- add local notation scoped to the remaining commands
      adapt_reader (λ cfg : elaborator_config, {cfg with local_notations := nota::cfg.local_notations}) $ do {
        (update_parser_config : coelaborator),
        yield_to_outside,
        commands.elaborate n
      }
    } else elab_and_recurse
  | _ := elab_and_recurse

def section.elaborate : coelaborator :=
do sec ← view «section» <$> current_command,
   let sec_name := syntax_ident.val <$> sec.name,
   yield_to_outside,
   commands.elaborate tt 1000,
   -- local notations may have vanished
   update_parser_config,
   end_sec ← view «end» <$> current_command,
   let end_sec_name := syntax_ident.val <$> end_sec.name,
   when (sec_name ≠ end_sec_name) $
     error (review «end» end_sec) $ "invalid end of section, expected name '" ++
       to_string (sec_name.get_or_else name.anonymous) ++ "'"

def namespace.elaborate : coelaborator :=
do ns ← view «namespace» <$> current_command,
   let ns_name := ns.name.val,
   yield_to_outside,
   commands.elaborate tt 1000,
   -- local notations may have vanished
   update_parser_config,
   end_ns ← view «end» <$> current_command,
   let end_ns_name := syntax_ident.val <$> end_ns.name,
   when (some ns_name ≠ end_ns_name) $
     error (review «end» end_ns) $ "invalid end of namespace, expected name '" ++
       to_string ns_name ++ "'"

-- TODO(Sebastian): replace with attribute
def elaborators : rbmap name coelaborator (<) := rbmap.from_list [
  (notation.name, notation.elaborate),
  (reserve_notation.name, reserve_notation.elaborate),
  (section.name, section.elaborate),
  (namespace.name, namespace.elaborate),
  (declaration.name, declaration.elaborate)
] _

protected def max_recursion := 100
protected def max_commands := 10000

protected def run (cfg : elaborator_config) : coroutine syntax elaborator_state message_log :=
do
  let st := {elaborator_state . parser_cfg := cfg.initial_parser_cfg},
  p ← except_t.run $ flip state_t.run st $ flip reader_t.run cfg $ rec_t.run
    (commands.elaborate ff elaborator.max_commands)
    (λ _, modify $ λ st, {st with messages := st.messages.add {filename := "foo", pos := ⟨1,0⟩, text := "elaborator.run: out of fuel"}})
    (λ _, do
      cmd ← current_command,
      -- TODO(Sebastian): throw error on unknown command when we get serious
      some n ← pure cmd.as_node | pure (),
      some elab ← pure $ elaborators.find n.kind.name | pure (),
      catch elab $ λ e,
        modify $ λ st, {st with messages := st.messages.add e})
    elaborator.max_recursion,
  match p with
  | except.ok ((), st) := pure st.messages
  | except.error e     := pure $ message_log.empty.add e

end elaborator
end lean
