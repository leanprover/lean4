/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Parser for the Lean language
-/
prelude
import init.lean.parser.parsec init.lean.parser.syntax
import init.lean.parser.identifier init.data.rbmap

/-- A small wrapper of `reader_t` that simplifies introducing and invoking
    recursion points in a computation. -/
-- TODO(Sebastian): move?
def rec_t (α δ : Type) (m : Type → Type) (β : Type) :=
reader_t (α → m δ) m β

namespace rec_t
variables {m : Type → Type} {α δ β : Type} [monad m]
local attribute [reducible] rec_t

/-- Continue at the recursion point stored at `run`. -/
def recurse (a : α) : rec_t α δ m δ :=
do x ← read,
   monad_lift (x a)

variables (base : α → m δ) (rec : α → rec_t α δ m δ)
private def run_aux : nat → α → m δ
| 0     := base
| (n+1) := λ a, (rec a).run (run_aux n)

/-- Execute `rec a`, re-executing it whenever `recurse` (with a new `a`) is called.
    After `max_rec` recursion steps, `base` is executed instead. -/
protected def run (a : α) (max_rec := 1000) : m δ :=
(rec a).run (run_aux base rec max_rec)

-- not clear how to auto-derive these given the additional constraints
instance : monad (rec_t α δ m) := infer_instance
instance [alternative m] : alternative (rec_t α δ m) := infer_instance
instance : has_monad_lift m (rec_t α δ m) := infer_instance
instance (ε) [monad_except ε m] : monad_except ε (rec_t α δ m) := infer_instance
instance (μ) [alternative m] [lean.parser.monad_parsec μ m] : lean.parser.monad_parsec μ (rec_t α δ m) :=
infer_instance
end rec_t

class monad_rec (α δ : out_param Type) (m : Type → Type) :=
(recurse {} : α → m δ)
export monad_rec (recurse)

instance monad_rec.trans (α δ m m') [has_monad_lift m m'] [monad_rec α δ m] [monad m] : monad_rec α δ m' :=
{ recurse := λ a, monad_lift (recurse a : m δ) }

instance monad_rec.base (α δ m) [monad m] : monad_rec α δ (rec_t α δ m) :=
{ recurse := rec_t.recurse }

namespace lean
-- TODO: enhance massively
abbreviation message := string

namespace parser

inductive trie.node (α : Type)
| mk : option α → list (char × trie.node) → trie.node

def trie (α : Type) := rbmap char (trie.node α) (<)

namespace trie
variables {α : Type}

protected def node.empty : trie.node α := ⟨none, []⟩

protected def mk : trie α := mk_rbmap _ _ _

private def update_child (c : char) (f : trie.node α → trie.node α) : list (char × trie.node α) → list (char × trie.node α)
| []           := [(c, f trie.node.empty)]
| ((c',t)::ts) := if c = c' then (c', f t)::ts else (c',t)::update_child ts

private def insert_aux (val : α) : nat → trie.node α → string.iterator → trie.node α
| 0     ⟨_,   ts⟩ _  := ⟨some val, ts⟩   -- NOTE: overrides old value
| (n+1) ⟨val, ts⟩ it :=
  ⟨val, update_child it.curr (λ t, insert_aux n t it.next) ts⟩

def insert (t : trie α) (s : string) (val : α) : trie α :=
let it := s.mk_iterator in
let t' := (t.find it.curr).get_or_else trie.node.empty in
let it' := it.next in
t.insert it.curr (insert_aux val it'.remaining t' it')

private def match_prefix_aux : nat → trie.node α → string.iterator → option (string.iterator × α) → option (string.iterator × α)
| 0 ⟨val, ts⟩ it acc := prod.mk it <$> val <|> acc
| (n+1) ⟨val, ts⟩ it acc :=
  let acc' := prod.mk it <$> val <|> acc in
  match ts.assoc it.curr with
  | some t := match_prefix_aux n t it.next acc'
  | none   := acc'

def match_prefix {α : Type} (t : trie α) (it : string.iterator) : option (string.iterator × α) :=
do t' ← t.find it.curr,
   let it' := it.next,
   match_prefix_aux it'.remaining t' it' none
end trie


/- Maximum standard precedence. This is the precedence of function application.
   In the standard Lean language, only the token `.` has a left-binding power greater
   than `max_prec` (so that field accesses like `g (h x).f` are parsed as `g ((h x).f)`,
   not `(g (h x)).f`). -/
def max_prec : nat := 1024

structure token_config :=
(«prefix» : string)
/- Left-binding power used by the term parser. The term parser operates in the context
   of a right-binding power between 0 (used by parentheses and on the top-level) and
   (usually) `max_prec` (used by function application). After parsing an initial term,
   it continues parsing and expanding that term only when the left-binding power of
   the next token is greater than the current right-binding power. For example, it
   never continues parsing an argument after the initial parse, unless a token with
   lbp > max_prec is encountered. Conversely, the term parser will always continue
   parsing inside parentheses until it finds a token with lbp 0 (such as `)`). -/
(lbp : nat)
-- reading a token should not need any state
/- An optional parser that is activated after matching `prefix`.
   It should return a syntax tree with a "hole" for the
   `source_info` surrounding the token, which will be supplied
   by the `token` parser. -/
(token_parser : option (parsec' (source_info → syntax)) := none)

structure parser_state :=
(tokens : trie token_config)
-- note: stored in reverse for efficient append
(errors : list lean.message)
/- Start position of the current token. This might not be equal to the parser
   position for two reasons:
   * We plan to eagerly parse leading whitespace so as not to do so multiple times
   * During error recovery, skipped input should be associated to the next token -/
(token_start : string.iterator)

structure parser_config := mk

@[derive monad alternative monad_reader monad_state monad_parsec monad_except]
def parser_t (m : Type → Type) [monad m] := reader_t parser_config $ state_t parser_state $ parsec_t syntax m
abbreviation basic_parser_m := parser_t id
abbreviation basic_parser := basic_parser_m syntax

 -- an arbitrary `parser` type; parsers are usually some monad stack based on `basic_parser_m` returning `syntax`
variable {ρ : Type}

class has_tokens (r : ρ) := mk {} ::
(tokens : list token_config)

open parser.has_tokens (tokens)

instance list.nil.tokens : parser.has_tokens ([] : list ρ) :=
⟨[]⟩
instance list.cons.tokens (r : ρ) (rs : list ρ) [parser.has_tokens r] [parser.has_tokens rs] :
  parser.has_tokens (r::rs) :=
⟨tokens r ++ tokens rs⟩

protected class has_view (r : ρ) (α : out_param Type) :=
(view : syntax → option α)
(review : α → syntax)

instance has_view.default (r : ρ) : inhabited (parser.has_view r syntax) :=
⟨{ view := some, review := id }⟩

class syntax_node_kind.has_view (k : syntax_node_kind) (α : out_param Type) :=
(view : syntax → option α)
(review : α → syntax)

section
local attribute [reducible] parser_t
protected def run {m : Type → Type} [monad m] (cfg : parser_config) (st : parser_state) (s : string) (r : parser_t m syntax) :
  m (syntax × list message) :=
do r ← ((r.run cfg).run st).parse_with_eoi s,
   pure $ match r with
   | except.ok (a, st) := (a, st.errors.reverse)
   | except.error msg  := (msg.custom, [to_string msg])
end

open monad_parsec
open parser.has_view
variables {α : Type} {m : Type → Type}
local notation `parser` := m syntax

def log_error [monad_state parser_state m] (e : message) : m unit :=
modify (λ st, {st with errors := to_string e :: st.errors})

def eoi : syntax_node_kind := ⟨`lean.parser.parser.eoi⟩

protected def parse [monad m] (cfg : parser_config) (s : string) (r : parser_t m syntax) [parser.has_tokens r] :
  m (syntax × list message) :=
-- the only hardcoded tokens, because they are never directly mentioned by a `parser`
let builtin_tokens : list token_config := [⟨"/-", 0, none⟩, ⟨"--", 0, none⟩] in
let trie := (tokens r ++ builtin_tokens).foldl (λ t cfg, trie.insert t cfg.prefix cfg) trie.mk in
parser.run cfg ⟨trie, [], s.mk_iterator⟩ s $ do
  stx ← catch r $ λ (msg : parsec.message _), do {
    modify $ λ st, {st with token_start := msg.it},
    parser.log_error (to_string msg),
    pure msg.custom
  },
  whitespace,
  -- add `eoi` node and store any residual input in its prefix
  catch monad_parsec.eoi $ λ msg, parser.log_error (to_string msg),
  tk_start ← parser_state.token_start <$> get,
  let stop := tk_start.to_end in
  pure $ syntax.node ⟨none, [
    stx,
    syntax.node ⟨eoi, [syntax.atom ⟨some ⟨⟨tk_start, stop⟩, stop.offset, ⟨stop, stop⟩⟩, atomic_val.string ""⟩]⟩
  ]⟩

structure parse.view_ty :=
(root : syntax)
(eoi  : syntax)

def parse.view : syntax → option parse.view_ty
| (syntax.node ⟨none, [root, eoi]⟩) := some ⟨root, eoi⟩
| _ := none

namespace combinators
variables [monad m] [monad_except (parsec.message syntax) m] [monad_parsec syntax m] [alternative m]

def node' (k : option syntax_node_kind) (rs : list parser) : parser :=
do (args, _) ← rs.mfoldl (λ (p : list syntax × nat) r, do
     (args, remaining) ← pure p,
     -- on error, append partial syntax tree and `missing` objects to previous successful parses and rethrow
     a ← catch r $ λ msg,
       let args := list.repeat syntax.missing (remaining-1) ++ msg.custom :: args in
       throw {msg with custom := syntax.node ⟨k, args.reverse⟩},
     pure (a::args, remaining - 1)
   ) ([], rs.length),
   pure $ syntax.node ⟨k, args.reverse⟩

@[reducible] def seq : list parser → parser := node' none
@[reducible] def node (k : syntax_node_kind) : list parser → parser := node' k

instance node'.tokens (k) (rs : list parser) [parser.has_tokens rs] : parser.has_tokens (node' k rs) :=
⟨tokens rs⟩

instance node.view (k) (rs : list parser) [i : syntax_node_kind.has_view k α] : parser.has_view (node k rs) α :=
{ view := i.view, review := i.review }

private def many1_aux (p : parser) : list syntax → nat → parser
| as 0     := error "unreachable"
| as (n+1) := do a ← catch p (λ msg, throw {msg with custom :=
                       -- append `syntax.missing` to make clear that list is incomplete
                       syntax.node ⟨none, (syntax.missing::msg.custom::as).reverse⟩}),
              many1_aux (a::as) n <|> pure (syntax.node ⟨none, (a::as).reverse⟩)

def many1 (r : parser) : parser :=
do rem ← remaining, many1_aux r [] (rem+1)

instance many1.tokens (r : parser) [parser.has_tokens r] : parser.has_tokens (many1 r) :=
⟨tokens r⟩

instance many1.view (r : parser) [parser.has_view r α] : parser.has_view (many1 r) (list α) :=
{ view := λ stx, match stx with
    | syntax.missing := list.ret <$> view r syntax.missing
    | syntax.node ⟨none, stxs⟩ := stxs.mmap (view r)
    | _ := failure,
  review := λ as, syntax.node ⟨none, as.map (review r)⟩ }

def many (r : parser) : parser :=
many1 r <|> pure (syntax.node ⟨none, []⟩)

instance many.tokens (r : parser) [parser.has_tokens r] : parser.has_tokens (many r) :=
⟨tokens r⟩

instance many.view (r : parser) [has_view r α] : parser.has_view (many r) (list α) :=
{..many1.view r}

def optional (r : parser) : parser :=
do r ← optional $
     -- on error, wrap in "some"
     catch r (λ msg, throw {msg with custom := syntax.node ⟨none, [msg.custom]⟩}),
   pure $ match r with
   | some r := syntax.node ⟨none, [r]⟩
   | none   := syntax.node ⟨none, []⟩

instance optional.tokens (r : parser) [parser.has_tokens r] : parser.has_tokens (optional r) :=
⟨tokens r⟩

inductive optional_view (α : Type)
| some (a : α) : optional_view
| none {} : optional_view
| missing {} : optional_view

namespace optional_view
instance : functor optional_view :=
{ map := λ _ _ f v, match v with
  | some a  := some (f a)
  | none    := none
  | missing := missing }
end optional_view

instance optional.view (r : parser) [parser.has_view r α] : parser.has_view (optional r) (optional_view α) :=
{ view := λ stx, match stx with
    | syntax.missing := pure optional_view.missing
    | syntax.node ⟨none, []⟩ := pure optional_view.none
    | syntax.node ⟨none, [stx]⟩ := optional_view.some <$> view r stx
    | _ := failure,
  review := λ a, match a with
    | optional_view.some a  := syntax.node ⟨none, [review r a]⟩
    | optional_view.none    := syntax.node ⟨none, []⟩
    | optional_view.missing := syntax.missing }

/-- Parse a list `[p1, ..., pn]` of parsers as `p1 <|> ... <|> pn`.
    Note that there is NO explicit encoding of which parser was chosen;
    parsers should instead produce distinct node names for disambiguation. -/
def any_of (rs : list parser) : parser :=
match rs with
| [] := error "any_of"
| (r::rs) := rs.foldl (<|>) r

instance any_of.tokens (rs : list parser) [parser.has_tokens rs] : parser.has_tokens (any_of rs) :=
⟨tokens rs⟩

instance any_of.view (rs : list parser) : parser.has_view (any_of rs) syntax := default _

/-- Parse a list `[p1, ..., pn]` of parsers as `p1 <|> ... <|> pn`.
    The result will be wrapped in a node with the the index of the successful
    parser as the name. -/
def choice (rs : list parser) : parser :=
rs.enum.foldr
  (λ ⟨i, r⟩ r', (λ stx, syntax.node ⟨some ⟨name.mk_numeral name.anonymous i⟩, [stx]⟩) <$> r <|> r')
  -- use `foldr` so that any other error is preferred over this one
  (error "choice: empty list")

instance choice.tokens (rs : list parser) [parser.has_tokens rs] : parser.has_tokens (choice rs) :=
⟨tokens rs⟩

instance try.tokens (r : parser) [parser.has_tokens r] : parser.has_tokens (try r) :=
⟨tokens r⟩
instance try.view (r : parser) [i : parser.has_view r α] : parser.has_view (try r) α :=
{..i}

instance label.tokens (r : parser) (l) [parser.has_tokens r] : parser.has_tokens (label r l) :=
⟨tokens r⟩
instance label.view (r : parser) (l) [i : parser.has_view r α] : parser.has_view (label r l) α :=
{..i}

instance dbg.tokens (r : parser) (l) [parser.has_tokens r] : parser.has_tokens (dbg l r) :=
⟨tokens r⟩
instance dbg.view (r  : parser) (l) [i : parser.has_view r α] : parser.has_view (dbg l r) α :=
{..i}

instance recurse.tokens (α δ m a) [monad_rec α δ m] : parser.has_tokens (recurse a : m δ) :=
⟨[]⟩ -- recursive use should not contribute any new tokens
instance recurse.view (α δ m a) [monad_rec α δ m] : parser.has_view (recurse a : m δ) syntax := default _

def with_recurse {α : Type} (init : α) (r : α → rec_t α syntax m syntax) : parser :=
rec_t.run (λ _, error "recursion limit") r init

instance monad_lift.tokens {m' : Type → Type} [has_monad_lift_t m m'] (r : m syntax) [parser.has_tokens r] :
  parser.has_tokens (monad_lift r : m' syntax) :=
⟨tokens r⟩
instance monad_lift.view {m' : Type → Type} [has_monad_lift_t m m'] (r : m syntax) [i : parser.has_view r α] :
  parser.has_view (monad_lift r : m' syntax) α :=
{..i}

end combinators
end «parser»
end lean
