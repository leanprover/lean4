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
def message := string

namespace parser

structure reader_state :=
(fatal : bool)
(errors : list lean.message)

def reader_state.empty : reader_state :=
⟨ff, []⟩

structure reader_config := mk

@[irreducible] def reader := reader_t reader_config $ state_t reader_state $ parser

namespace reader
local attribute [reducible] reader
instance : monad reader := infer_instance
instance : alternative reader := infer_instance
instance : monad_parser reader := infer_instance

protected def parse (cfg : reader_config) (st : reader_state) (s : string) (r : reader syntax) :
  except parser.message syntax :=
prod.fst <$> ((r.run cfg).run st).parse s
end reader

namespace reader
open monad_parser

def ident : reader syntax :=
do start ← pos,
   n ← identifier,
   stop ← pos,
   whitespace,
   pure $ syntax.ident ⟨some ⟨start, stop⟩, n, none, none⟩

-- TODO(Sebastian): proper tokenization
def symbol (sym : string) (trailing_ws : bool := tt) : reader syntax :=
do start ← pos,
   str sym,
   stop ← pos,
   when trailing_ws whitespace,
   pure $ syntax.atom ⟨some ⟨start, stop⟩, atomic_val.string sym⟩

def keyword (kw : string) : reader syntax :=
symbol kw

def num : reader syntax :=
do start ← pos,
   n ← monad_parser.num,
   stop ← pos,
   whitespace,
   pure $ syntax.atom ⟨some ⟨start, stop⟩, atomic_val.number n⟩

def node (m : macro) (ps : list (reader syntax)) : reader syntax :=
do args ← ps.mmap id,
   pure $ syntax.node ⟨m.name, args⟩

def many (p : reader syntax) : reader syntax :=
do args ← many p,
   pure $ syntax.node ⟨name.anonymous, args⟩

def optional (p : reader syntax) : reader syntax :=
do r ← optional p,
   pure $ match r with
   | some r := syntax.node ⟨name.anonymous, [r]⟩
   | none   := syntax.node ⟨name.anonymous, []⟩

end reader

open reader

def «prelude» := {macro . name := `prelude}

def prelude.reader : reader syntax :=
node «prelude» [keyword "prelude"]

def import_path := {macro . name := `import_path}

def import_path.reader : reader syntax :=
node import_path [optional (many (symbol "." ff)), ident]

def «import» := {macro . name := `import}

def import.reader : reader syntax :=
node «import» [keyword "import", many import_path.reader]

def «theory» := {macro . name := `theory}

def theory.reader : reader syntax :=
node «theory» [optional (keyword "noncomputable"), keyword "theory"]

def module := {macro . name := `module}

def module.reader : reader syntax :=
node module [
  optional prelude.reader,
  many import.reader,
  optional theory.reader
]

end parser
end lean
