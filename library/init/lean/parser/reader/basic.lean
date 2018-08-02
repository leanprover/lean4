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

/-- Continue at the recursion point stored at `with_recurse`. -/
def recurse : rec_t r m r :=
do x ← read,
   monad_lift x

variables (base : m r) (rec : rec_t r m r)
private def with_recurse_aux : nat → m r
| 0     := base
| (n+1) := rec.run (with_recurse_aux n)

/-- Execute `rec`, re-executing it whenever `recurse` is called.
    After `max_rec` recursion steps, `base` is executed instead. -/
def with_recurse (max_rec := 1000) : rec_t r m r :=
⟨λ _, rec.run (with_recurse_aux base rec max_rec)⟩

-- not clear how to auto-derive these given the additional constraints
instance : monad (rec_t r m) := infer_instance
instance [alternative m] : alternative (rec_t r m) := infer_instance
instance : has_monad_lift m (rec_t r m) := infer_instance
instance (ε) [monad_except ε m] : monad_except ε (rec_t r m) := infer_instance
instance (μ) [alternative m] [lean.parser.monad_parsec μ m] : lean.parser.monad_parsec μ (rec_t r m) :=
infer_instance
end rec_t

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

@[irreducible, derive monad alternative monad_reader monad_state monad_parsec monad_except]
def read_m := rec_t syntax $ reader_t reader_config $ state_t reader_state $ parsec syntax

structure reader :=
(read : read_m syntax)
(tokens : list token_config := [])

namespace read_m
local attribute [reducible] read_m
protected def run (cfg : reader_config) (st : reader_state) (s : string) (r : read_m syntax) :
  syntax × list message :=
match (((r.run (monad_parsec.error "no recursive parser at top level")).run cfg).run st).parse_with_eoi s with
| except.ok (a, st) := (a, st.errors.reverse)
| except.error msg  := (msg.custom, [to_string msg])

def log_error (e : message) : read_m unit :=
modify (λ st, {st with errors := to_string e :: st.errors})
end read_m

namespace reader
open monad_parsec

protected def parse (cfg : reader_config) (s : string) (r : reader) :
  syntax × list message :=
-- the only hardcoded tokens, because they are never directly mentioned by a `reader`
let tokens : list token_config := [⟨"/-", none⟩, ⟨"--", none⟩] in
do {
  stx ← catch r.read $ λ (msg : parsec.message _), do {
    modify $ λ st, {st with token_start := msg.it},
    read_m.log_error (to_string msg),
    pure msg.custom
  },
  whitespace,
  -- add `eoi` node and store any residual input in its prefix
  catch eoi $ λ msg, read_m.log_error (to_string msg),
  tk_start ← reader_state.token_start <$> get,
  let stop := tk_start.to_end in
  pure $ syntax.node ⟨name.anonymous, [
    stx,
    syntax.node ⟨`eoi, [syntax.atom ⟨some ⟨⟨tk_start, stop⟩, stop.offset, ⟨stop, stop⟩⟩, atomic_val.string ""⟩]⟩
  ]⟩
}.run cfg ⟨r.tokens ++ tokens, [], s.mk_iterator⟩ s

namespace combinators
def node' (m : name) (rs : list reader) : reader :=
{ read := do {
    (args, _) ← rs.mfoldl (λ (p : list syntax × nat) r, do
      (args, remaining) ← pure p,
      -- on error, append partial syntax tree and `missing` objects to previous successful parses and rethrow
      a ← catch r.read $ λ msg,
        let args := list.repeat syntax.missing (remaining-1) ++ msg.custom :: args in
        throw {msg with custom := syntax.node ⟨m, args.reverse⟩},
      pure (a::args, remaining - 1)
    ) ([], rs.length),
    pure $ syntax.node ⟨m, args.reverse⟩
  },
  tokens := rs.bind reader.tokens }

def seq := node' name.anonymous
def node (m : macro) := node' m.name

private def many1_aux (p : read_m syntax) : list syntax → nat → read_m syntax
| as 0     := error "unreachable"
| as (n+1) := do a ← catch p (λ msg, throw {msg with custom :=
                       -- append `syntax.missing` to make clear that list is incomplete
                       syntax.node ⟨name.anonymous, (syntax.missing::msg.custom::as).reverse⟩}),
              many1_aux (a::as) n <|> pure (syntax.node ⟨name.anonymous, (a::as).reverse⟩)

def many1 (r : reader) : reader :=
{ r with read := do rem ← remaining, many1_aux r.read [] (rem+1) }

def many (r : reader) : reader :=
{ r with read := (many1 r).read <|> pure (syntax.node ⟨name.anonymous, []⟩) }

def optional (r : reader) : reader :=
{ r with read := do
    r ← optional $
      -- on error, wrap in "some"
      catch r.read (λ msg, throw {msg with custom := syntax.node ⟨name.anonymous, [msg.custom]⟩}),
    pure $ match r with
    | some r := syntax.node ⟨name.anonymous, [r]⟩
    | none   := syntax.node ⟨name.anonymous, []⟩ }

/-- Parse a list `[p1, ..., pn]` of readers as `p1 <|> ... <|> pn`.
    Note that there is NO explicit encoding of which reader was chosen;
    readers should instead produce distinct node names for disambiguation. -/
def any_of (rs : list reader) : reader :=
{ read   := (match rs with
    | [] := error "any_of"
    | (r::rs) := (rs.map reader.read).foldl (<|>) r.read),
  tokens := (rs.map reader.tokens).join }

def try (r : reader) : reader :=
{ r with read := try r.read }

def label (r : reader) (l : string) : reader :=
{ r with read := label r.read l }

infixr <?> := label

def dbg (label : string) (r : reader) : reader :=
{ r with read := dbg label r.read }

local attribute [reducible] read_m
def recurse : reader :=
{ read   := rec_t.recurse,
  tokens := [] } -- recursive use should not contribute any new tokens

def with_recurse (r : reader) : reader :=
{ r with read := rec_t.with_recurse (error "recursion limit") r.read }
end combinators
end reader
end parser
end lean
