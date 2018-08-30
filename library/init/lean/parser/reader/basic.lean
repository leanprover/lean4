/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Reader for the Lean language
-/
prelude
import init.lean.parser.parsec init.lean.parser.syntax init.lean.parser.macro
import init.lean.parser.identifier

/-- A small wrapper of `reader_t` that simplifies introducing and invoking
    recursion points in a computation. -/
-- TODO(Sebastian): move?
def rec_t (r : Type) (m : Type → Type) (α : Type) :=
reader_t (m r) m α

namespace rec_t
variables {m : Type → Type} {r α : Type} [monad m]
local attribute [reducible] rec_t

/-- Continue at the recursion point stored at `run`. -/
def recurse : rec_t r m r :=
do x ← read,
   monad_lift x

variables (base : m r) (rec : rec_t r m r)
private def run_aux : nat → m r
| 0     := base
| (n+1) := rec.run (run_aux n)

/-- Execute `rec`, re-executing it whenever `recurse` is called.
    After `max_rec` recursion steps, `base` is executed instead. -/
protected def run (max_rec := 1000) : m r :=
rec.run (run_aux base rec max_rec)

-- not clear how to auto-derive these given the additional constraints
instance : monad (rec_t r m) := infer_instance
instance [alternative m] : alternative (rec_t r m) := infer_instance
instance : has_monad_lift m (rec_t r m) := infer_instance
instance (ε) [monad_except ε m] : monad_except ε (rec_t r m) := infer_instance
instance (μ) [alternative m] [lean.parser.monad_parsec μ m] : lean.parser.monad_parsec μ (rec_t r m) :=
infer_instance
end rec_t

class monad_rec (r : out_param Type) (m : Type → Type) :=
(recurse {} : m r)
export monad_rec (recurse)

instance monad_rec.base (r m) [monad m] : monad_rec r (rec_t r m) :=
{ recurse := rec_t.recurse }

instance monad_rec.trans (r m m') [has_monad_lift m m'] [monad_rec r m] [monad m] : monad_rec r m' :=
{ recurse := monad_lift (recurse : m r) }

namespace lean
-- TODO: enhance massively
abbreviation message := string

namespace parser

structure token_config :=
(«prefix» : string)
-- reading a token should not need any state
/- An optional parser that is activated after matching `prefix`.
   It should return a syntax tree with a "hole" for the
   `source_info` surrounding the token, which will be supplied
   by the `token` reader. -/
(token_reader : option (parsec' (source_info → syntax)) := none)

structure reader_state :=
(tokens : list token_config)
-- note: stored in reverse for efficient append
(errors : list lean.message)
/- Start position of the current token. This might not be equal to the parser
   position for two reasons:
   * We plan to eagerly parse leading whitespace so as not to do so multiple times
   * During error recovery, skipped input should be associated to the next token -/
(token_start : string.iterator)

structure reader_config := mk

@[derive monad alternative monad_reader monad_state monad_parsec monad_except]
def read_t (m : Type → Type) [monad m] := reader_t reader_config $ state_t reader_state $ parsec_t syntax m
abbreviation basic_read_m := read_t id
abbreviation basic_reader := basic_read_m syntax

 -- an arbitrary `reader` type; readers are usually some monad stack based on `basic_read_m` returning `syntax`
variable {ρ : Type}

class reader.has_tokens (r : ρ) := mk {} ::
(tokens : list token_config)

open reader.has_tokens (tokens)

instance list.nil.tokens : reader.has_tokens ([] : list ρ) :=
⟨[]⟩
instance list.cons.tokens (r : ρ) (rs : list ρ) [reader.has_tokens r] [reader.has_tokens rs] :
  reader.has_tokens (r::rs) :=
⟨tokens r ++ tokens rs⟩

class reader.has_view (r : ρ) (α : out_param Type) :=
(view : syntax → option α)
(review : α → syntax)

instance reader.has_view.default (r : ρ) : inhabited (reader.has_view r syntax) :=
⟨{ view := some, review := id }⟩

class syntax_node_kind.has_view (k : syntax_node_kind) (α : out_param Type) :=
(view : syntax → option α)
(review : α → syntax)

section
local attribute [reducible] read_t
protected def reader.run {m : Type → Type} [monad m] (cfg : reader_config) (st : reader_state) (s : string) (r : read_t m syntax) :
  m (syntax × list message) :=
do r ← ((r.run cfg).run st).parse_with_eoi s,
   pure $ match r with
   | except.ok (a, st) := (a, st.errors.reverse)
   | except.error msg  := (msg.custom, [to_string msg])
end

namespace reader
open monad_parsec
open reader.has_view
variables {α : Type} {m : Type → Type}
local notation `reader` := m syntax

def log_error [monad_state reader_state m] (e : message) : m unit :=
modify (λ st, {st with errors := to_string e :: st.errors})

def eoi : syntax_node_kind := ⟨`lean.parser.reader.eoi⟩

protected def parse [monad m] (cfg : reader_config) (s : string) (r : read_t m syntax) [reader.has_tokens r] :
  m (syntax × list message) :=
-- the only hardcoded tokens, because they are never directly mentioned by a `reader`
let builtin_tokens : list token_config := [⟨"/-", none⟩, ⟨"--", none⟩] in
reader.run cfg ⟨tokens r ++ builtin_tokens, [], s.mk_iterator⟩ s $ do
  stx ← catch r $ λ (msg : parsec.message _), do {
    modify $ λ st, {st with token_start := msg.it},
    reader.log_error (to_string msg),
    pure msg.custom
  },
  whitespace,
  -- add `eoi` node and store any residual input in its prefix
  catch monad_parsec.eoi $ λ msg, reader.log_error (to_string msg),
  tk_start ← reader_state.token_start <$> get,
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

def node' (k : option syntax_node_kind) (rs : list reader) : reader :=
do (args, _) ← rs.mfoldl (λ (p : list syntax × nat) r, do
     (args, remaining) ← pure p,
     -- on error, append partial syntax tree and `missing` objects to previous successful parses and rethrow
     a ← catch r $ λ msg,
       let args := list.repeat syntax.missing (remaining-1) ++ msg.custom :: args in
       throw {msg with custom := syntax.node ⟨k, args.reverse⟩},
     pure (a::args, remaining - 1)
   ) ([], rs.length),
   pure $ syntax.node ⟨k, args.reverse⟩

@[reducible] def seq : list reader → reader := node' none
@[reducible] def node (k : syntax_node_kind) : list reader → reader := node' k

instance node'.tokens (k) (rs : list reader) [reader.has_tokens rs] : reader.has_tokens (node' k rs) :=
⟨tokens rs⟩

instance node.view (k) (rs : list reader) [i : syntax_node_kind.has_view k α] : reader.has_view (node k rs) α :=
{ view := i.view, review := i.review }

private def many1_aux (p : reader) : list syntax → nat → reader
| as 0     := error "unreachable"
| as (n+1) := do a ← catch p (λ msg, throw {msg with custom :=
                       -- append `syntax.missing` to make clear that list is incomplete
                       syntax.node ⟨none, (syntax.missing::msg.custom::as).reverse⟩}),
              many1_aux (a::as) n <|> pure (syntax.node ⟨none, (a::as).reverse⟩)

def many1 (r : reader) : reader :=
do rem ← remaining, many1_aux r [] (rem+1)

instance many1.tokens (r : reader) [reader.has_tokens r] : reader.has_tokens (many1 r) :=
⟨tokens r⟩

instance many1.view (r : reader) [reader.has_view r α] : reader.has_view (many1 r) (list α) :=
{ view := λ stx, match stx with
    | syntax.missing := list.ret <$> view r syntax.missing
    | syntax.node ⟨none, stxs⟩ := stxs.mmap (view r)
    | _ := failure,
  review := λ as, syntax.node ⟨none, as.map (review r)⟩ }

def many (r : reader) : reader :=
many1 r <|> pure (syntax.node ⟨none, []⟩)

instance many.tokens (r : reader) [reader.has_tokens r] : reader.has_tokens (many r) :=
⟨tokens r⟩

instance many.view (r : reader) [has_view r α] : reader.has_view (many r) (list α) :=
{..many1.view r}

def optional (r : reader) : reader :=
do r ← optional $
     -- on error, wrap in "some"
     catch r (λ msg, throw {msg with custom := syntax.node ⟨none, [msg.custom]⟩}),
   pure $ match r with
   | some r := syntax.node ⟨none, [r]⟩
   | none   := syntax.node ⟨none, []⟩

instance optional.tokens (r : reader) [reader.has_tokens r] : reader.has_tokens (optional r) :=
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

instance optional.view (r : reader) [reader.has_view r α] : reader.has_view (optional r) (optional_view α) :=
{ view := λ stx, match stx with
    | syntax.missing := pure optional_view.missing
    | syntax.node ⟨none, []⟩ := pure optional_view.none
    | syntax.node ⟨none, [stx]⟩ := optional_view.some <$> view r stx
    | _ := failure,
  review := λ a, match a with
    | optional_view.some a  := syntax.node ⟨none, [review r a]⟩
    | optional_view.none    := syntax.node ⟨none, []⟩
    | optional_view.missing := syntax.missing }

/-- Parse a list `[p1, ..., pn]` of readers as `p1 <|> ... <|> pn`.
    Note that there is NO explicit encoding of which reader was chosen;
    readers should instead produce distinct node names for disambiguation. -/
def any_of (rs : list reader) : reader :=
match rs with
| [] := error "any_of"
| (r::rs) := rs.foldl (<|>) r

instance any_of.tokens (rs : list reader) [reader.has_tokens rs] : reader.has_tokens (any_of rs) :=
⟨tokens rs⟩

instance any_of.view (rs : list reader) : reader.has_view (any_of rs) syntax := default _

/-- Parse a list `[p1, ..., pn]` of readers as `p1 <|> ... <|> pn`.
    The result will be wrapped in a node with the the index of the successful
    parser as the name. -/
def choice (rs : list reader) : reader :=
rs.enum.foldr
  (λ ⟨i, r⟩ r', (λ stx, syntax.node ⟨some ⟨name.mk_numeral name.anonymous i⟩, [stx]⟩) <$> r <|> r')
  -- use `foldr` so that any other error is preferred over this one
  (error "choice: empty list")

instance choice.tokens (rs : list reader) [reader.has_tokens rs] : reader.has_tokens (choice rs) :=
⟨tokens rs⟩

instance try.tokens (r : reader) [reader.has_tokens r] : reader.has_tokens (try r) :=
⟨tokens r⟩
instance try.view (r : reader) [i : reader.has_view r α] : reader.has_view (try r) α :=
{..i}

instance label.tokens (r : reader) (l) [reader.has_tokens r] : reader.has_tokens (label r l) :=
⟨tokens r⟩
instance label.view (r : reader) (l) [i : reader.has_view r α] : reader.has_view (label r l) α :=
{..i}

instance dbg.tokens (r : reader) (l) [reader.has_tokens r] : reader.has_tokens (dbg l r) :=
⟨tokens r⟩
instance dbg.view (r  : reader) (l) [i : reader.has_view r α] : reader.has_view (dbg l r) α :=
{..i}

instance recurse.tokens (r m) [monad_rec r m] : reader.has_tokens (recurse : m r) :=
⟨[]⟩ -- recursive use should not contribute any new tokens
instance recurse.view (r m) [monad_rec r m] : reader.has_view (recurse : m r) syntax := default _

def with_recurse (r : rec_t syntax m syntax) : reader :=
rec_t.run (error "recursion limit") r

instance with_recurse.tokens (r : rec_t syntax m syntax) [reader.has_tokens r] : reader.has_tokens (with_recurse r) :=
⟨tokens r⟩
instance with_recurse.view (r : rec_t syntax m syntax) [i : reader.has_view r α] : reader.has_view (with_recurse r) α :=
{..i}

instance monad_lift.tokens {m' : Type → Type} [has_monad_lift_t m m'] (r : m syntax) [reader.has_tokens r] :
  reader.has_tokens (monad_lift r : m' syntax) :=
⟨tokens r⟩
instance monad_lift.view {m' : Type → Type} [has_monad_lift_t m m'] (r : m syntax) [i : reader.has_view r α] :
  reader.has_view (monad_lift r : m' syntax) α :=
{..i}

end combinators
end «reader»
end parser
end lean
