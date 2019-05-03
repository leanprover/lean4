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

namespace Lean
namespace Parser

/- Maximum standard precedence. This is the precedence of Function application.
   In the standard Lean language, only the token `.` has a left-binding power greater
   than `maxPrec` (so that field accesses like `g (h x).f` are parsed as `g ((h x).f)`,
   not `(g (h x)).f`). -/
def maxPrec : Nat := 1024

structure TokenConfig :=
(«prefix» : String)
/- Left-binding power used by the Term Parser. The Term Parser operates in the context
   of a right-binding power between 0 (used by parentheses and on the top-Level) and
   (usually) `maxPrec` (used by Function application). After parsing an initial Term,
   it continues parsing and expanding that Term only when the left-binding power of
   the next token is greater than the current right-binding power. For example, it
   never continues parsing an argument after the initial parse, unless a token with
   lbp > maxPrec is encountered. Conversely, the Term Parser will always continue
   parsing inside parentheses until it finds a token with lbp 0 (such as `)`). -/
(lbp : Nat := 0)
-- reading a token should not need any State
/- An optional Parser that is activated after matching `prefix`.
   It should return a Syntax tree with a "hole" for the
   `SourceInfo` surrounding the token, which will be supplied
   by the `token` Parser.

   Remark: `suffixParser` has many applications for example for parsing
   hexdecimal numbers, `prefix` is `0x` and `suffixParser` is the Parser `digit*`.
   We also use it to parse String literals: here `prefix` is just `"`.
-/
(suffixParser : Option (Parsec' (SourceInfo → Syntax)) := none)

-- Backtrackable State
structure ParserState :=
(messages : MessageLog)

structure TokenCacheEntry :=
(startIt stopIt : String.OldIterator)
(tk : Syntax)

-- Non-backtrackable State
structure ParserCache :=
(tokenCache : Option TokenCacheEntry := none)
-- for profiling
(hit miss : Nat := 0)

structure FrontendConfig :=
(filename : String)
(input    : String)
(fileMap  : FileMap)

/- Remark: if we have a Node in the Trie with `some TokenConfig`, the String induced by the path is equal to the `TokenConfig.prefix`. -/
structure ParserConfig extends FrontendConfig :=
(tokens : Trie TokenConfig)

instance parserConfigCoe : HasCoe ParserConfig FrontendConfig :=
⟨ParserConfig.toFrontendConfig⟩

@[derive Monad Alternative MonadParsec MonadExcept]
def parserCoreT (m : Type → Type) [Monad m] :=
ParsecT Syntax $ StateT ParserCache $ m

@[derive Monad Alternative MonadReader MonadParsec MonadExcept]
def ParserT (ρ : Type) (m : Type → Type) [Monad m] := ReaderT ρ $ parserCoreT m
@[derive Monad Alternative MonadReader MonadParsec MonadExcept]
def BasicParserM := ParserT ParserConfig Id
abbrev basicParser := BasicParserM Syntax
abbrev monadBasicParser := HasMonadLiftT BasicParserM

section
local attribute [reducible] BasicParserM ParserT parserCoreT
@[inline] def getCache : BasicParserM ParserCache :=
monadLift (get : StateT ParserCache Id _)

@[inline] def putCache : ParserCache → BasicParserM PUnit :=
λ c, monadLift (set c : StateT ParserCache Id _)
end

 -- an arbitrary `Parser` Type; parsers are usually some Monad stack based on `BasicParserM` returning `Syntax`
variable {ρ : Type}

class HasTokens (r : ρ) := mk {} ::
(tokens : List TokenConfig)

@[noinline, nospecialize] def tokens (r : ρ) [HasTokens r] :=
HasTokens.tokens r

instance HasTokens.Inhabited (r : ρ) : Inhabited (HasTokens r) :=
⟨⟨[]⟩⟩

instance List.nil.tokens : Parser.HasTokens ([] : List ρ) :=
default _

instance List.cons.tokens (r : ρ) (rs : List ρ) [Parser.HasTokens r] [Parser.HasTokens rs] :
  Parser.HasTokens (r::rs) :=
⟨tokens r ++ tokens rs⟩

class HasView (α : outParam Type) (r : ρ) :=
(view : Syntax → α)
(review : α → Syntax)

export HasView (view review)

def tryView {α : Type} (k : SyntaxNodeKind) [HasView α k] (stx : Syntax) : Option α :=
if stx.isOfKind k then some (HasView.view k stx) else none

instance HasView.default (r : ρ) : Inhabited (Parser.HasView Syntax r) :=
⟨{ view := id, review := id }⟩

class HasViewDefault (r : ρ) (α : outParam Type) [HasView α r] (default : α) := mk {}

def messageOfParsecMessage {μ : Type} (cfg : FrontendConfig) (msg : Parsec.Message μ) : Message :=
{filename := cfg.filename, pos := cfg.fileMap.toPosition msg.it.offset, text := msg.text}

/-- Run Parser stack, returning a partial Syntax tree in case of a fatal error -/
protected def run {m : Type → Type} {α ρ : Type} [Monad m] [HasCoeT ρ FrontendConfig] (cfg : ρ) (s : String) (r : StateT ParserState (ParserT ρ m) α) :
m (Sum α Syntax × MessageLog) :=
do (r, _) ← (((r.run {messages:=MessageLog.empty}).run cfg).parse s).run {},
pure $ match r with
| Except.ok (a, st) := (Sum.inl a, st.messages)
| Except.error msg  := (Sum.inr msg.custom.get, MessageLog.empty.add (messageOfParsecMessage cfg msg))

open MonadParsec
open Parser.HasView
variables {α : Type} {m : Type → Type}
local notation `Parser` := m Syntax

def logMessage {μ : Type} [Monad m] [MonadReader ρ m] [HasLiftT ρ FrontendConfig] [MonadState ParserState m]
  (msg : Parsec.Message μ) : m Unit :=
do cfg ← read,
   modify (λ st, {st with messages := st.messages.add (messageOfParsecMessage ↑cfg msg)})

def mkTokenTrie (tokens : List TokenConfig) : Except String (Trie TokenConfig) :=
do -- the only hardcoded tokens, because they are never directly mentioned by a `Parser`
   let builtinTokens : List TokenConfig := [{«prefix» := "/-"}, {«prefix» := "--"}],
   t ← (builtinTokens ++ tokens).mfoldl (λ (t : Trie TokenConfig) tk,
     match t.find tk.prefix with
     | some tk' := match tk.lbp, tk'.lbp with
       | l, 0  := pure $ t.insert tk.prefix tk
       | 0, _  := pure t
       | l, l' := if l = l' then pure t else throw $
         "invalid token '" ++ tk.prefix ++ "', has been defined with precedences " ++
         toString l ++ " and " ++ toString l'
     | none := pure $ t.insert tk.prefix tk)
     Trie.empty,
   pure t


/- Monad stacks used in multiple files -/

/- NOTE: We move `RecT` under `ParserT`'s `ReaderT` so that `termParser`, which does not
   have access to `commandParser`'s ρ (=`CommandParserConfig`) can still recurse into it
   (for command quotations). This means that the `CommandParserConfig` will be reset
   on a recursive call to `command.Parser`, i.e. it forgets about locally registered parsers,
   but that's not an issue for our intended uses of it. -/
@[derive Monad Alternative MonadReader MonadParsec MonadExcept MonadRec]
def CommandParserM (ρ : Type) := ReaderT ρ $ RecT Unit Syntax $ parserCoreT Id

section
local attribute [reducible] ParserT CommandParserM
instance CommandParserM.MonadReaderAdapter (ρ ρ' : Type) :
  MonadReaderAdapter ρ ρ' (CommandParserM ρ) (CommandParserM ρ') :=
inferInstance
instance CommandParserM.basicParser (ρ : Type) [HasLiftT ρ ParserConfig] : monadBasicParser (CommandParserM ρ) :=
⟨λ _ x cfg rec, x.run ↑cfg⟩
end

/- The `Nat` at `RecT` is the lbp` -/
@[derive Monad Alternative MonadReader MonadParsec MonadExcept MonadRec monadBasicParser]
def TermParserM := RecT Nat Syntax $ CommandParserM ParserConfig
abbrev termParser := TermParserM Syntax

/-- A Term Parser for a suffix or infix notation that accepts a preceding Term. -/
@[derive Monad Alternative MonadReader MonadParsec MonadExcept MonadRec monadBasicParser]
def TrailingTermParserM := ReaderT Syntax TermParserM
abbrev trailingTermParser := TrailingTermParserM Syntax

instance trailingTermParserCoe : HasCoe termParser trailingTermParser :=
⟨λ x _, x⟩

/-- A multimap indexed by tokens. Used for indexing parsers by their leading token. -/
def TokenMap (α : Type) := RBMap Name (List α) Name.quickLt

def TokenMap.insert {α : Type} (map : TokenMap α) (k : Name) (v : α) : TokenMap α :=
match map.find k with
| none    := map.insert k [v]
| some vs := map.insert k (v::vs)

def TokenMap.ofList {α : Type} : List (Name × α) → TokenMap α
| []          := mkRBMap _ _ _
| (⟨k,v⟩::xs) := (TokenMap.ofList xs).insert k v

instance tokenMapNil.tokens : Parser.HasTokens $ @TokenMap.ofList ρ [] :=
default _

instance tokenMapCons.tokens (k : Name) (r : ρ) (rs : List (Name × ρ)) [Parser.HasTokens r] [Parser.HasTokens $ TokenMap.ofList rs] :
  Parser.HasTokens $ TokenMap.ofList ((k,r)::rs) :=
⟨tokens r ++ tokens (TokenMap.ofList rs)⟩

-- This needs to be a separate structure since `termParser`s cannot contain themselves in their config
structure CommandParserConfig extends ParserConfig :=
(leadingTermParsers : TokenMap termParser)
(trailingTermParsers : TokenMap trailingTermParser)
-- local Term parsers (such as from `local notation`) hide previous parsers instead of overloading them
(localLeadingTermParsers : TokenMap termParser := mkRBMap _ _ _)
(localTrailingTermParsers : TokenMap trailingTermParser := mkRBMap _ _ _)

instance commandParserConfigCoeParserConfig : HasCoe CommandParserConfig ParserConfig :=
⟨CommandParserConfig.toParserConfig⟩

abbrev commandParser := CommandParserM CommandParserConfig Syntax

end «Parser»
end Lean
