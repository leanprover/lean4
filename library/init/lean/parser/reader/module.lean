/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Module-level readers and macros
-/
prelude
import init.lean.parser.reader.token init.lean.parser.reader.term init.data.list.instances

namespace lean.parser
namespace reader
open combinators monad_parsec
open reader.has_view

def symbol_coe : has_coe string reader := ⟨symbol⟩
def seq_coe : has_coe_t (list reader) reader := ⟨seq⟩
local attribute [instance] symbol_coe seq_coe

-- coerce all list literals to `list reader`
local notation `[` l:(foldr `, ` (h t, @list.cons reader h t) list.nil `]`) := l

instance (r rs α) [i : reader.has_view (seq (r::rs)) α] : reader.has_view (r::rs : list reader) α := i

local postfix `?`:10000 := optional
local postfix *:10000 := many
local postfix +:10000 := many1

def «prelude» := {macro . name := `prelude}

def prelude.reader : reader :=
node «prelude» ["prelude"]

def import_path := {macro . name := `import_path}

@[derive reader.has_view]
def import_path.reader : reader :=
-- use `raw_symbol` to ignore registered tokens like ".."
node import_path [(raw_symbol ".")*, ident]

structure import_path.view :=
(dirups : list syntax)
(ident  : syntax)

instance import_path.has_view : import_path.has_view import_path.view :=
{ view := λ stx, function.uncurry import_path.view.mk <$> view import_path.reader stx,
  review := λ ⟨a, b⟩, review import_path.reader (a, b) }

def «import» := {macro . name := `import}

@[derive reader.has_view]
def import.reader : reader :=
node «import» ["import", import_path.reader+]

structure import.view :=
(«import» : syntax)
(paths : list syntax)

instance import.has_view : import.has_view import.view :=
{ view := λ stx, function.uncurry import.view.mk <$> view import.reader stx,
  review := λ ⟨a, b⟩, review import.reader (a, b) }

section commands

def «open» := {macro . name := `open}

def open_export.reader : reader :=
[ident,
 ["as", ident]?,
 [try ["(", ident], ident*, ")"]?,
 [try ["(", "renaming"], [ident, "->", ident]+, ")"]?,
 ["(", "hiding", ident+, ")"]?
]+

def open.reader : reader :=
node «open» ["open", open_export.reader]

def «section» := {macro . name := `section}

def section.reader : reader :=
node «section» ["section", ident?, recurse*, "end", ident?]

def «universe» := {macro . name := `universe}

def universe.reader :=
node «universe» [any_of [
  -- local
  [try ["universe", "variables"], ident+],
  -- global
  [any_of [["universes", ident+], ["universe", ident]]]
]]

def «notation» := {macro . name := `notation}

@[derive reader.has_view]
def prec : reader := [":", number]/-TODO <|> expr-/

def quoted_symbol : read_m syntax :=
do (s, info) ← with_source_info $ take_until (= '`'),
   pure $ syntax.atom ⟨info, atomic_val.string s⟩

def notation_quoted_symbol := {macro . name := `notation_symbol}

@[derive reader.has_view]
def notation_quoted_symbol.reader : reader :=
[raw_symbol "`", {read := quoted_symbol}, raw_symbol "`", prec?]

structure notation_quoted_symbol.view :=
(left_quote : syntax)
(symbol : syntax)
(right_quote : syntax)
(prec : optional_view (syntax × syntax))

instance notation_quoted_symbol.has_view : notation_quoted_symbol.has_view notation_quoted_symbol.view :=
{ view := λ stx, do { (a, b, c, d) ← view notation_quoted_symbol.reader stx, pure $ notation_quoted_symbol.view.mk a b c d },
  review := λ ⟨a, b, c, d⟩, review notation_quoted_symbol.reader (a, b, c, d) }

@[derive reader.has_view]
def notation_symbol : reader :=
any_of [
  notation_quoted_symbol.reader
  --TODO, {read := do tk ← token, /- check if reserved token-/}
]

@[derive reader.has_view]
def action : reader :=
[":", any_of [
  number,
  "max",
  "prev",
  "scoped"
  /-TODO seq [
    "(",
    any_of ["foldl", "foldr"],
    optional prec,
    notation_tk,-/]]

@[derive reader.has_view]
def arg_transition : reader :=
[ident, action?]

@[derive reader.has_view]
def transition :=
any_of [
 ["binder", prec?],
 ["binders", prec?],
 arg_transition
]

@[derive reader.has_view]
def rule : reader :=
[notation_symbol, transition?]

@[derive reader.has_view]
def rules : reader :=
[ident?, rule*]

@[derive reader.has_view]
def notation_spec : reader :=
any_of [
  number,
  rules
]

@[derive has_view]
def notation.reader : reader :=
node «notation» ["notation", notation_spec, ":=", term.reader]

structure notation.view :=
(«notation» : syntax)
(spec : syntax)
(assign : syntax)
(term : syntax)

instance notation.has_view : notation.has_view notation.view :=
{ view := λ stx, do { (a, b, c, d) ← view notation.reader stx, pure $ notation.view.mk a b c d },
  review := λ ⟨a, b, c, d⟩, review notation.reader (a, b, c, d) }

def reserve_notation : macro := {macro . name := `reserve_notation}

def reserve_notation.reader : reader :=
node «reserve_notation» [try ["reserve", "notation"], notation_spec]

def mixfix : macro := {macro . name := `mixfix}

@[derive has_view]
def mixfix.reader : reader :=
node «mixfix» [
  any_of ["prefix", "infix", "infixl", "infixr", "postfix"],
  notation_symbol, ":=", term.reader]

structure mixfix.view :=
(kind : syntax)
(notation_symbol : syntax)
(assign : syntax)
(term : syntax)

instance mixfix.has_view : mixfix.has_view mixfix.view :=
{ view := λ stx, do { (a, b, c, d) ← view mixfix.reader stx, pure $ mixfix.view.mk a b c d },
  review := λ ⟨a, b, c, d⟩, review mixfix.reader (a, b, c, d) }

def reserve_mixfix : macro := {macro . name := `reserve_mixfix}

def reserve_mixfix.reader : reader :=
node «reserve_mixfix» [
  try ["reserve", any_of ["prefix", "infix", "infixl", "infixr", "postfix"]],
  notation_symbol]

def command.reader :=
with_recurse $ any_of [open.reader, section.reader, universe.reader, notation.reader, reserve_notation.reader,
  mixfix.reader, reserve_mixfix.reader] <?> "command"

/-- Read commands, recovering from errors inside commands (attach partial syntax tree)
    as well as unknown commands (skip input). -/
private def commands_aux : bool → list syntax → nat → read_m syntax
| recovering cs 0            := error "unreachable"
-- on end of input, return list of parsed commands
| recovering cs (nat.succ n) := (eoi *> pure (syntax.node ⟨name.anonymous, cs.reverse⟩)) <|> do
  (recovering, c) ← catch (do {
    c ← command.reader.read,
    pure (ff, some c)
  } <|> do {
      -- unknown command: try to skip token, or else single character
      when (¬ recovering) $ do {
        it ← left_over,
        read_m.log_error $ to_string { parsec.message . expected := dlist.singleton "command", it := it, custom := () }
      },
      tk_start ← reader_state.token_start <$> get,
      -- since the output of the following parser is never captured in a syntax tree...
      try (token *> pure ()) <|> (any *> pure ()),
      -- ...restore `token_start` after it
      modify $ λ st, {st with token_start := tk_start},
      pure (tt, none)
    }) $ λ msg, do {
      -- error inside command: log error, return partial syntax tree
      modify $ λ st, {st with token_start := msg.it},
      read_m.log_error (to_string msg),
      pure (tt, some msg.custom)
    },
  commands_aux recovering (c.to_monad++cs) n

def commands.reader : reader :=
{ read := do { rem ← remaining, commands_aux ff [] rem.succ },
  tokens := command.reader.tokens }

-- custom reader requires custom instance
instance commands.reader.has_view : commands.reader.has_view (list syntax) :=
{..many.view command.reader}

end commands

def module := {macro . name := `module}

@[derive reader.has_view]
def module.reader : reader :=
node module [prelude.reader?, import.reader*, commands.reader]

structure module.view :=
(«prelude» : optional_view syntax)
(imports   : list syntax)
(commands  : list syntax)

instance module.has_view : module.has_view module.view :=
{ view := λ stx, do { (a, b, c) ← view module.reader stx, pure $ module.view.mk a b c },
  review := λ ⟨a, b, c⟩, review module.reader (a, b, c) }

end reader

namespace reader
open macro.has_view combinators

instance string_syntax_coe : has_coe string syntax :=
⟨λ s, syntax.atom ⟨none, atomic_val.string s⟩⟩

instance name_syntax_coe : has_coe name syntax :=
⟨λ n, syntax.ident ⟨none, n, none, none⟩⟩

def mixfix.expand (stx : syntax) : option syntax :=
do v ← view mixfix stx,
   syntax.atom ⟨_, atomic_val.string kind⟩ ← pure v.kind | failure,
   -- TODO: reserved token case
   prec ← notation_quoted_symbol.view.prec <$> view notation_quoted_symbol v.notation_symbol,
   let spec := reader.has_view.review notation_spec $ match kind with
     | "prefix" := reader.has_view.review rules (optional_view.none, [
         reader.has_view.review rule (v.notation_symbol, optional_view.some $
           reader.has_view.review arg_transition (`b, prec))
       ])
     | _ := sorry,
   pure $ review «notation» (⟨"notation", spec, ":=", v.term⟩ : notation.view)

end reader
end lean.parser
