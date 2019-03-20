/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Parser for the Lean language
-/
prelude
import init.lean.parser.parsec init.lean.parser.syntax init.lean.parser.rec
import init.lean.parser.trie
import init.lean.parser.identifier init.data.rbmap init.lean.message

namespace lean
namespace parser

/- Maximum standard precedence. This is the precedence of function application.
   In the standard Lean language, only the token `.` has a left-binding power greater
   than `maxPrec` (so that field accesses like `g (h x).f` are parsed as `g ((h x).f)`,
   not `(g (h x)).f`). -/
def maxPrec : nat := 1024

structure tokenConfig :=
(«prefix» : string)
/- Left-binding power used by the term parser. The term parser operates in the context
   of a right-binding power between 0 (used by parentheses and on the top-level) and
   (usually) `maxPrec` (used by function application). After parsing an initial term,
   it continues parsing and expanding that term only when the left-binding power of
   the next token is greater than the current right-binding power. For example, it
   never continues parsing an argument after the initial parse, unless a token with
   lbp > maxPrec is encountered. Conversely, the term parser will always continue
   parsing inside parentheses until it finds a token with lbp 0 (such as `)`). -/
(lbp : nat := 0)
-- reading a token should not need any state
/- An optional parser that is activated after matching `prefix`.
   It should return a syntax tree with a "hole" for the
   `sourceInfo` surrounding the token, which will be supplied
   by the `token` parser.

   Remark: `suffixParser` has many applications for example for parsing
   hexdecimal numbers, `prefix` is `0x` and `suffixParser` is the parser `digit*`.
   We also use it to parse string literals: here `prefix` is just `"`.
-/
(suffixParser : option (parsec' (sourceInfo → syntax)) := none)

-- Backtrackable state
structure parserState :=
(messages : messageLog)

structure tokenCacheEntry :=
(startIt stopIt : string.iterator)
(tk : syntax)

-- Non-backtrackable state
structure parserCache :=
(tokenCache : option tokenCacheEntry := none)
-- for profiling
(hit miss : nat := 0)

structure frontendConfig :=
(filename : string)
(input    : string)
(fileMap : fileMap)

/- Remark: if we have a node in the trie with `some tokenConfig`, the string induced by the path is equal to the `tokenConfig.prefix`. -/
structure parserConfig extends frontendConfig :=
(tokens : trie tokenConfig)

instance parserConfigCoe : hasCoe parserConfig frontendConfig :=
⟨parserConfig.toFrontendConfig⟩

@[derive monad alternative monadParsec monadExcept]
def parserCoreT (m : Type → Type) [monad m] :=
parsecT syntax $ stateT parserCache $ m

@[derive monad alternative monadReader monadParsec monadExcept]
def parserT (ρ : Type) (m : Type → Type) [monad m] := readerT ρ $ parserCoreT m
@[derive monad alternative monadReader monadParsec monadExcept]
def basicParserM := parserT parserConfig id
abbrev basicParser := basicParserM syntax
abbrev monadBasicParser := hasMonadLiftT basicParserM

section
local attribute [reducible] basicParserM parserT parserCoreT
@[inline] def getCache : basicParserM parserCache :=
monadLift (get : stateT parserCache id _)

@[inline] def putCache : parserCache → basicParserM punit :=
λ c, monadLift (put c : stateT parserCache id _)
end

 -- an arbitrary `parser` type; parsers are usually some monad stack based on `basicParserM` returning `syntax`
variable {ρ : Type}

class hasTokens (r : ρ) := mk {} ::
(tokens : list tokenConfig)

@[noinline, nospecialize] def tokens (r : ρ) [hasTokens r] :=
hasTokens.tokens r

instance hasTokens.inhabited (r : ρ) : inhabited (hasTokens r) :=
⟨⟨[]⟩⟩

instance list.nil.tokens : parser.hasTokens ([] : list ρ) :=
default _

instance list.cons.tokens (r : ρ) (rs : list ρ) [parser.hasTokens r] [parser.hasTokens rs] :
  parser.hasTokens (r::rs) :=
⟨tokens r ++ tokens rs⟩

class hasView (α : outParam Type) (r : ρ) :=
(view : syntax → α)
(review : α → syntax)

export hasView (view review)

def tryView {α : Type} (k : syntaxNodeKind) [hasView α k] (stx : syntax) : option α :=
if stx.isOfKind k then some (hasView.view k stx) else none

instance hasView.default (r : ρ) : inhabited (parser.hasView syntax r) :=
⟨{ view := id, review := id }⟩

class hasViewDefault (r : ρ) (α : outParam Type) [hasView α r] (default : α) := mk {}

def messageOfParsecMessage {μ : Type} (cfg : frontendConfig) (msg : parsec.message μ) : message :=
{filename := cfg.filename, pos := cfg.fileMap.toPosition msg.it.offset, text := msg.text}

/-- Run parser stack, returning a partial syntax tree in case of a fatal error -/
protected def run {m : Type → Type} {α ρ : Type} [monad m] [hasCoeT ρ frontendConfig] (cfg : ρ) (s : string) (r : stateT parserState (parserT ρ m) α) :
m (sum α syntax × messageLog) :=
do (r, _) ← (((r.run {messages:=messageLog.empty}).run cfg).parse s).run {},
pure $ match r with
| except.ok (a, st) := (sum.inl a, st.messages)
| except.error msg  := (sum.inr msg.custom.get, messageLog.empty.add (messageOfParsecMessage cfg msg))

open monadParsec
open parser.hasView
variables {α : Type} {m : Type → Type}
local notation `parser` := m syntax

def logMessage {μ : Type} [monad m] [monadReader ρ m] [hasLiftT ρ frontendConfig] [monadState parserState m]
  (msg : parsec.message μ) : m unit :=
do cfg ← read,
   modify (λ st, {st with messages := st.messages.add (messageOfParsecMessage ↑cfg msg)})

def mkTokenTrie (tokens : list tokenConfig) : except string (trie tokenConfig) :=
do -- the only hardcoded tokens, because they are never directly mentioned by a `parser`
   let builtinTokens : list tokenConfig := [{«prefix» := "/-"}, {«prefix» := "--"}],
   t ← (builtinTokens ++ tokens).mfoldl (λ (t : trie tokenConfig) tk,
     match t.find tk.prefix with
     | some tk' := (match tk.lbp, tk'.lbp with
       | l, 0  := pure $ t.insert tk.prefix tk
       | 0, _  := pure t
       | l, l' := if l = l' then pure t else throw $
         "invalid token '" ++ tk.prefix ++ "', has been defined with precedences " ++
         toString l ++ " and " ++ toString l')
     | none := pure $ t.insert tk.prefix tk)
     trie.mk,
   pure t


/- Monad stacks used in multiple files -/

/- NOTE: We move `recT` under `parserT`'s `readerT` so that `termParser`, which does not
   have access to `commandParser`'s ρ (=`commandParserConfig`) can still recurse into it
   (for command quotations). This means that the `commandParserConfig` will be reset
   on a recursive call to `command.parser`, i.e. it forgets about locally registered parsers,
   but that's not an issue for our intended uses of it. -/
@[derive monad alternative monadReader monadParsec monadExcept monadRec]
def commandParserM (ρ : Type) := readerT ρ $ recT unit syntax $ parserCoreT id

section
local attribute [reducible] parserT commandParserM
instance commandParserM.monadReaderAdapter (ρ ρ' : Type) :
  monadReaderAdapter ρ ρ' (commandParserM ρ) (commandParserM ρ') :=
inferInstance
instance commandParserM.basicParser (ρ : Type) [hasLiftT ρ parserConfig] : monadBasicParser (commandParserM ρ) :=
⟨λ _ x cfg rec, x.run ↑cfg⟩
end

/- The `nat` at `recT` is the lbp` -/
@[derive monad alternative monadReader monadParsec monadExcept monadRec monadBasicParser]
def termParserM := recT nat syntax $ commandParserM parserConfig
abbrev termParser := termParserM syntax

/-- A term parser for a suffix or infix notation that accepts a preceding term. -/
@[derive monad alternative monadReader monadParsec monadExcept monadRec monadBasicParser]
def trailingTermParserM := readerT syntax termParserM
abbrev trailingTermParser := trailingTermParserM syntax

instance trailingTermParserCoe : hasCoe termParser trailingTermParser :=
⟨λ x _, x⟩

local attribute [instance] name.hasLtQuick
/-- A multimap indexed by tokens. Used for indexing parsers by their leading token. -/
def tokenMap (α : Type) := rbmap name (list α) (<)

def tokenMap.insert {α : Type} (map : tokenMap α) (k : name) (v : α) : tokenMap α :=
match map.find k with
| none    := map.insert k [v]
| some vs := map.insert k (v::vs)

def tokenMap.ofList {α : Type} : list (name × α) → tokenMap α
| []          := mkRbmap _ _ _
| (⟨k,v⟩::xs) := (tokenMap.ofList xs).insert k v

instance tokenMapNil.tokens : parser.hasTokens $ @tokenMap.ofList ρ [] :=
default _

instance tokenMapCons.tokens (k : name) (r : ρ) (rs : list (name × ρ)) [parser.hasTokens r] [parser.hasTokens $ tokenMap.ofList rs] :
  parser.hasTokens $ tokenMap.ofList ((k,r)::rs) :=
⟨tokens r ++ tokens (tokenMap.ofList rs)⟩

-- This needs to be a separate structure since `termParser`s cannot contain themselves in their config
structure commandParserConfig extends parserConfig :=
(leadingTermParsers : tokenMap termParser)
(trailingTermParsers : tokenMap trailingTermParser)
-- local term parsers (such as from `local notation`) hide previous parsers instead of overloading them
(localLeadingTermParsers : tokenMap termParser := mkRbmap _ _ _)
(localTrailingTermParsers : tokenMap trailingTermParser := mkRbmap _ _ _)

instance commandParserConfigCoeParserConfig : hasCoe commandParserConfig parserConfig :=
⟨commandParserConfig.toParserConfig⟩

abbrev commandParser := commandParserM commandParserConfig syntax

end «parser»
end lean
