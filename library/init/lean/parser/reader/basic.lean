/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Reader for the Lean language
-/
prelude
import init.lean.parser.parser_t init.lean.parser.syntax init.lean.parser.macro
import init.lean.parser.identifier

namespace lean
-- TODO: enhance massively
def message := string

namespace parser

structure token_config :=
(«prefix» : string)
-- reading a token should not need any state
(token_reader : option (position → parser syntax) := none)

structure reader_state :=
(tokens : list token_config)
(fatal : bool)
(errors : list lean.message)

def reader_state.empty : reader_state :=
⟨[], ff, []⟩

structure reader_config := mk

@[irreducible] def reader := reader_t reader_config $ state_t reader_state $ parser

namespace reader
local attribute [reducible] reader
instance : monad reader := infer_instance
instance : alternative reader := infer_instance
instance : monad_reader reader_config reader := infer_instance
instance : monad_state reader_state reader := infer_instance
instance : monad_parser reader := infer_instance

protected def parse (cfg : reader_config) (st : reader_state) (s : string) (r : reader syntax) :
  except parser.message syntax :=
prod.fst <$> ((r.run cfg).run st).parse_with_eoi s
end reader

namespace reader
open monad_parser

def node (m : macro) (ps : list (reader syntax)) : reader syntax :=
do args ← ps.mmap id,
   pure $ syntax.node ⟨m.name, args⟩

def many (p : reader syntax) : reader syntax :=
do args ← many p,
   pure $ syntax.node ⟨name.anonymous, args⟩

def many1 (p : reader syntax) : reader syntax :=
do args ← many1 p,
   pure $ syntax.node ⟨name.anonymous, args⟩

def optional (p : reader syntax) : reader syntax :=
do r ← optional p,
   pure $ match r with
   | some r := syntax.node ⟨name.anonymous, [r]⟩
   | none   := syntax.node ⟨name.anonymous, []⟩

end reader
end parser
end lean
