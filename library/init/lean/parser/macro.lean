/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich
-/
prelude
import init.lean.parser.move
import init.lean.parser.syntax

namespace lean.parser

local attribute [instance] name.has_lt_quick

@[irreducible] def parse_m (r σ) := except_t string $ reader_t r $ state σ

namespace parse_m
section
local attribute [reducible] parse_m

instance (r σ) : monad (parse_m r σ) := by apply_instance
--instance (r σ) : monad_run _ (parse_m r σ) := by apply_instance
instance (r σ) : monad_except string (parse_m r σ) := by apply_instance
instance (r σ) : monad_reader r (parse_m r σ) := by apply_instance
instance (r σ) : monad_state σ (parse_m r σ) := by apply_instance
instance (r σ σ') : monad_state_adapter σ σ' (parse_m r σ) (parse_m r σ') := by apply_instance
instance (r r' σ) : monad_reader_adapter r r' (parse_m r σ) (parse_m r' σ) := by apply_instance

def run {r σ α} (cfg : r) (st : σ) (x : parse_m r σ α) :=
(x.run.run cfg).run st
end

def run' {r σ α} (cfg : r) (st : σ): parse_m r σ α → except string α :=
λ x, prod.fst $ parse_m.run cfg st x
end parse_m

structure resolved :=
-- local or global
(decl : syntax_id ⊕ name)
/- prefix of the reference that corresponds to the decl. All trailing name components
   are field accesses. -/
(«prefix» : name)

meta instance resolved.has_to_format : has_to_format resolved := ⟨λ r, to_fmt (r.decl, r.prefix)⟩

structure resolve_cfg :=
(global_scope : rbmap name syntax)

@[reducible] def resolve_map := rbmap syntax_id resolved

structure resolve_state :=
(resolve_map : resolve_map)

def scope := rbmap (name × option macro_scope_id) syntax_id

@[reducible] def resolve_m := parse_m resolve_cfg resolve_state

def exp_fuel := 1000

structure macro :=
(name : name)
-- (read : reader)
-- TODO: What else does an expander need? How to model recursive expansion?
(expand : option (syntax_node syntax → syntax) := none)
(resolve : option (scope → syntax_node syntax → resolve_m (list scope)) := none)
-- (elaborate : list syntax → expr → tactic expr)

structure parse_state :=
(macros : rbmap name macro)
(resolve_cfg : resolve_cfg)

-- identifiers in macro expansions are annotated with incremental tags
structure expand_state :=
(next_tag : ℕ)

@[reducible] def exp_m := parse_m parse_state expand_state

def mk_tag : exp_m ℕ :=
do st ← get,
   put {st with next_tag := st.next_tag + 1},
   pure st.next_tag

def flip_tag (tag : ℕ) : syntax → syntax
| (syntax.node node) := syntax.node {node with args := (node.args.map
    -- flip_tag
    (λ s, flip_tag s))}
| (syntax.list ls) := syntax.list (ls.map
    -- flip_tag
    (λ s, flip_tag s))
| (syntax.ident ident@{msc := none, ..}) := syntax.ident {ident with msc := some tag}
| (syntax.ident ident@{msc := some tag', ..}) :=
    syntax.ident {ident with msc := if tag = tag' then none else some tag'}
| stx := stx

def expand : ℕ → syntax → exp_m syntax
| 0 _ := throw "macro expansion limit exceeded"
| (fuel + 1) (syntax.node node) :=
do cfg ← read,
   some {expand := some exp, ..} ← pure $ cfg.macros.find node.m
     | (λ args, syntax.node {node with args := args}) <$> node.args.mmap (expand fuel),
   tag ← mk_tag,
   let node := {node with args := node.args.map $ flip_tag tag},
   -- expand recursively
   expand fuel $ flip_tag tag $ exp node
| _ stx := pure stx

@[reducible] def resolve_m' := parse_m parse_state resolve_state

def resolve : scope → syntax → resolve_m' unit
| sc (syntax.node node) :=
do cfg ← read,
   some {resolve := some res, ..} ← pure $ cfg.macros.find node.m
     | node.args.mmap' $ resolve sc,
   arg_scopes ← adapt_reader parse_state.resolve_cfg $ res sc node,
   (arg_scopes.zip node.args).mmap' -- (uncurry resolve)
                                    (λ ⟨sc, stx⟩, resolve sc stx)
| _ _ := pure ()

def expand' (stx : syntax) : parse_m parse_state unit syntax :=
adapt_state (λ _, ({expand_state . next_tag := 0}, ())) (λ _, id) (expand 1000 stx)

def resolve' (stx : syntax) : parse_m parse_state unit (syntax × resolve_state) :=
let sc : scope := mk_rbmap _ _ _,
    st : resolve_state := ⟨mk_rbmap _ _ _⟩ in
    adapt_state (λ _, (st, ())) (λ _, id) $
    do resolve sc stx,
       rsm ← get,
       pure (stx, rsm)

end lean.parser
