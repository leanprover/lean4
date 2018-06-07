/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich
-/
prelude
import init.data.rbmap init.lean.parser.syntax init.control.combinators

namespace lean
namespace parser

local attribute [instance] name.has_lt_quick

@[irreducible] def parse_m (r σ) := except_t string $ reader_t r $ state σ

namespace parse_m
section
local attribute [reducible] parse_m

instance (r σ) : monad (parse_m r σ) := infer_instance
--instance (r σ) : monad_run _ (parse_m r σ) := by apply_instance
instance (r σ) : monad_except string (parse_m r σ) := infer_instance
instance (r σ) : monad_reader r (parse_m r σ)      := infer_instance
instance (r σ) : monad_state σ (parse_m r σ)       := infer_instance
instance (r σ σ') : monad_state_adapter σ σ' (parse_m r σ) (parse_m r σ')  := infer_instance
instance (r r' σ) : monad_reader_adapter r r' (parse_m r σ) (parse_m r' σ) := infer_instance

def run {r σ α} (cfg : r) (st : σ) (x : parse_m r σ α) :=
(x.run.run cfg).run st
end

def run' {r σ α} (cfg : r) (st : σ): parse_m r σ α → except string α :=
λ x, prod.fst $ parse_m.run cfg st x
end parse_m

structure resolve_cfg :=
(global_scope : rbmap name syntax (<))

def exp_fuel := 1000

structure macro :=
(name : name)
-- (read : reader)
-- TODO: What else does an expander need? How to model recursive expansion?
(expand : option (syntax_node syntax → option syntax) := none)
-- (elaborate : list syntax → expr → tactic expr)

structure parse_state :=
(macros : rbmap name macro (<))
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
| (syntax.ident ident@{msc := none, ..}) := syntax.ident {ident with msc := some tag}
| (syntax.ident ident@{msc := some tag', ..}) :=
    syntax.ident {ident with msc := if tag = tag' then none else some tag'}
| stx := stx

def expand : ℕ → syntax → exp_m syntax
| 0 _ := throw "macro expansion limit exceeded"
| (fuel + 1) (syntax.node node) :=
do cfg ← read,
   some {expand := some exp, ..} ← pure $ cfg.macros.find node.macro
     | (λ args, syntax.node {node with args := args}) <$> node.args.mmap (expand fuel),
   tag ← mk_tag,
   let node' := {node with args := node.args.map $ flip_tag tag},
   (match exp node' with
    -- expand recursively
    | some stx' := expand fuel $ flip_tag tag stx'
    | none := (λ args, syntax.node {node with args := args}) <$> node.args.mmap (expand fuel))
| _ stx := pure stx

def scope := rbmap (name × option macro_scope_id) var_offset (<)

def scope.insert (sc : scope) (id : syntax_ident) : scope :=
(sc.map (λ _ idx, idx + 1)).insert (id.name, id.msc) 0

def resolve_name (msc : option macro_scope_id) (sc : scope) : name → option resolved
| n@(name.mk_string n' s) :=
do {
  decl ← sc.find (n, msc),
  pure ⟨sum.inl decl, n⟩
} <|> resolve_name n'
| _ := none

def resolve : scope → syntax → parse_m parse_state unit syntax
-- TODO(Sebastian): move `match` back into primary pattern, use fuel if necessary
| sc (syntax.node n) := (match n with
  | ({macro := `bind, args := [syntax.node {macro := name.anonymous, args := vars}, body], ..}) :=
  do sc ← vars.mfoldl (λ sc var,
       do syntax.ident var ← pure var | throw "ill-shaped 'bind' macro",
          pure $ scope.insert sc var) sc,
     body ← resolve sc body,
     pure $ syntax.node {n with args := [syntax.node {macro := name.anonymous, args := vars}, body]}
  | _ :=
  do args ← n.args.mmap (resolve sc),
     pure $ syntax.node {n with args := args})
| sc (syntax.ident id) :=
do some res ← pure $ resolve_name id.msc sc id.name
     | throw ("unknown identifier " ++ id.name.to_string),
   pure $ syntax.ident {id with res := some res}
| _ stx := pure stx

def expand' (stx : syntax) : parse_m parse_state unit syntax :=
adapt_state (λ _, ({expand_state . next_tag := 0}, ())) (λ _, id) (expand 1000 stx)

def resolve' (stx : syntax) : parse_m parse_state unit syntax :=
let sc : scope := mk_rbmap _ _ _ in
resolve sc stx

end parser
end lean
