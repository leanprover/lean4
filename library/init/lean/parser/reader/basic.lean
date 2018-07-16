/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Reader for the Lean language
-/
prelude
import init.lean.parser.parsec init.lean.parser.syntax init.lean.parser.macro
import init.lean.parser.identifier

namespace lean
-- TODO: enhance massively
def message := string

namespace parser

structure token_config :=
(«prefix» : string)
-- reading a token should not need any state
/- An optional parser that is activated after matching `prefix`.
   It should return a syntax tree with a "hole" for the
   `source_info` surrounding the token, which will be supplied
   by the `token` reader. -/
(token_reader : option (parsec (source_info → syntax)) := none)

structure reader_state :=
(tokens : list token_config)
(fatal : bool)
(errors : list lean.message)

def reader_state.empty : reader_state :=
⟨[], ff, []⟩

structure reader_config := mk

@[irreducible] def read_m := reader_t reader_config $ state_t reader_state $ parsec

structure reader :=
(read : read_m syntax)
(tokens : list token_config := [])

namespace read_m
local attribute [reducible] read_m
instance : monad read_m := infer_instance
instance : alternative read_m := infer_instance
instance : monad_reader reader_config read_m := infer_instance
instance : monad_state reader_state read_m := infer_instance
instance : monad_parsec read_m := infer_instance

--TODO(Sebastian): expose `reader_state.errors`
protected def run {α : Type} (cfg : reader_config) (st : reader_state) (s : string) (r : read_m α) :
  except parsec.message α :=
prod.fst <$> ((r.run cfg).run st).parse_with_eoi s
end read_m

namespace reader
open monad_parsec

protected def parse (cfg : reader_config) (s : string) (r : reader) :
  except parsec.message syntax :=
-- the only hardcoded tokens, because they are never directly mentioned by a `reader`
let tokens : list token_config := [⟨"/-", none⟩, ⟨"--", none⟩] in
r.read.run cfg ⟨r.tokens ++ tokens, ff, []⟩ s

namespace combinators
def node' (m : name) (ps : list reader) : reader :=
{ read := do {
    args ← ps.mmap reader.read,
    pure $ syntax.node ⟨m, args⟩
  },
  tokens := ps.bind reader.tokens }

def seq := node' name.anonymous
def node (m : macro) := node' m.name

def many (p : reader) : reader :=
{ p with read := do
    args ← many p.read,
    pure $ syntax.node ⟨name.anonymous, args⟩ }

def many1 (p : reader) : reader :=
{ p with read := do
    args ← many1 p.read,
    pure $ syntax.node ⟨name.anonymous, args⟩ }

def optional (p : reader) : reader :=
{ p with read := do
    r ← optional p.read,
    pure $ match r with
    | some r := syntax.node ⟨name.anonymous, [r]⟩
    | none   := syntax.node ⟨name.anonymous, []⟩ }

def try (p : reader) : reader :=
{ p with read := try p.read }
end combinators
end reader
end parser
end lean
