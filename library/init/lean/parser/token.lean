/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Tokenizer for the Lean language

Even though our Parser architecture does not statically depend on a tokenizer but works directly on
the input String, we still use a "tokenizer" Parser in the Lean Parser in some circumstances:
* to distinguish between identifiers and keywords
* for error recovery: advance until next command token
* ...?
-/

prelude
import init.lean.parser.combinators init.lean.parser.stringliteral

namespace Lean
namespace Parser
open MonadParsec Combinators String HasView

def matchToken : BasicParserM (Option TokenConfig) :=
do cfg ← read,
   it ← leftOver,
   pure $ Prod.snd <$> cfg.tokens.oldMatchPrefix it

private def finishCommentBlockAux : Nat → Nat → BasicParserM Unit
| nesting (n+1) :=
  str "/-" *> finishCommentBlockAux (nesting + 1) n
  <|>
  str "-/" *> (if nesting = 1 then pure () else finishCommentBlockAux (nesting - 1) n)
  <|>
  any *> finishCommentBlockAux nesting n
| _ _ := error "unreachable"

def finishCommentBlock (nesting := 1) : BasicParserM Unit :=
do r ← remaining,
   finishCommentBlockAux nesting (r+1) <?> "end of comment block"

private def whitespaceAux : Nat → BasicParserM Unit
| (n+1) :=
do whitespace,
   str "--" *> takeWhile' (≠ '\n') *> whitespaceAux n
   <|>
   -- a "/--" doc comment is an actual token, not whitespace
   try (str "/-" *> notFollowedBy (str "-")) *> finishCommentBlock *> whitespaceAux n
   <|>
   pure ()
| 0 := error "unreachable"

variables {m : Type → Type}
local notation `Parser` := m Syntax
local notation `lift` := @monadLift BasicParserM _ _ _

/-- Skip whitespace and comments. -/
def whitespace : BasicParserM Unit :=
hidden $ do
  start ← leftOver,
  -- every `whitespaceAux` loop reads at least one Char
  whitespaceAux (start.remaining+1)

section
variables [Monad m] [MonadParsec Syntax m]

@[inline] def asSubstring {α : Type} (p : m α) : m Substring :=
do start ← leftOver,
   p,
   stop ← leftOver,
   pure ⟨start, stop⟩

variables [monadBasicParser m]

@[specialize] def updateLast (f : Syntax → Syntax) (trailing : Substring) : List Syntax → List Syntax
| []          := []
| [stx]       := [f stx]
| (stx::stxs) := stx :: updateLast stxs

private partial def updateTrailing : Substring → Syntax → Syntax
| trailing (Syntax.atom a@⟨some info, _⟩) := Syntax.atom {a with info := some {info with trailing := trailing}}
| trailing (Syntax.ident id@{info := some info, ..}) := Syntax.ident {id with info := some {info with trailing := trailing}}
| trailing (Syntax.rawNode n) := Syntax.rawNode {n with args := updateLast (updateTrailing trailing) trailing n.args}
| trailing stx := stx

def withTrailing (stx : Syntax) : m Syntax :=
do -- TODO(Sebastian): less greedy, more natural whitespace assignment
   -- E.g. only read up to the next line break
   trailing ← lift $ asSubstring $ whitespace,
   pure $ updateTrailing trailing stx

def mkRawRes (start stop : String.OldIterator) : Syntax :=
let ss : Substring := ⟨start, stop⟩ in
Syntax.atom ⟨some {leading := ⟨start, start⟩, pos := start.offset, trailing := ⟨stop, stop⟩}, ss.toString⟩

/-- Match an arbitrary Parser and return the consumed String in a `Syntax.atom`. -/
@[inline] def raw {α : Type} (p : m α) (trailingWs := false) : Parser := do
  start ← leftOver,
  p,
  stop ← leftOver,
  let stx := mkRawRes start stop,
  if trailingWs then withTrailing stx else pure stx

instance raw.tokens {α} (p : m α) (t) : Parser.HasTokens (raw p t : Parser) := default _
instance raw.view {α} (p : m α) (t) : Parser.HasView (Option SyntaxAtom) (raw p t : Parser) :=
{ view := λ stx, match stx with
  | Syntax.atom atom := some atom
  | _                := none,
  review := λ a, (Syntax.atom <$> a).getOrElse Syntax.missing }

/-- Like `raw (str s)`, but default to `s` in views. -/
@[inline, derive HasTokens HasView]
def rawStr (s : String) (trailingWs := false) : Parser :=
raw (str s) trailingWs

instance rawStr.viewDefault (s) (t) : Parser.HasViewDefault (rawStr s t : Parser) (Option SyntaxAtom) (some {val := s}) :=
⟨⟩

end

set_option class.instance_max_depth 200

@[derive HasTokens HasView]
def detailIdentPart.Parser : BasicParserM Syntax :=
nodeChoice! detailIdentPart {
  escaped: node! detailIdentPartEscaped [
    escBegin: rawStr idBeginEscape.toString,
    escaped: raw $ takeUntil1 isIdEndEscape,
    escEnd: rawStr idEndEscape.toString,
  ],
  default: raw $ satisfy isIdFirst *> takeWhile isIdRest
}

@[derive HasTokens HasView]
def detailIdentSuffix.Parser : RecT Unit Syntax BasicParserM Syntax :=
-- consume '.' only when followed by a character starting an detailIdentPart
try (lookahead (ch '.' *> (ch idBeginEscape <|> satisfy isIdFirst)))
*> node! detailIdentSuffix [«.»: rawStr ".", ident: recurse ()]

def detailIdent' : RecT Unit Syntax BasicParserM Syntax :=
node! detailIdent [part: monadLift detailIdentPart.Parser, suffix: optional detailIdentSuffix.Parser]

/-- A Parser that gives a more detailed View of `SyntaxIdent.rawVal`. Not used by default for
    performance reasons. -/
def detailIdent.Parser : BasicParserM Syntax :=
RecT.runParsec detailIdent' $ λ _, detailIdent'

private def ident' : basicParser :=
do
  start ← leftOver,
  s  ← idPart,
  n ← foldl Name.mkString (mkSimpleName s) $ do {
    -- consume '.' only when followed by a character starting an detailIdentPart
    try (lookahead (ch '.' *> (ch idBeginEscape <|> satisfy isIdFirst))),
    ch '.',
    idPart
  },
  stop ← leftOver,
  pure $ Syntax.ident {
    info := some {leading := ⟨start, start⟩, pos := start.offset, trailing := ⟨stop, stop⟩},
    rawVal := ⟨start, stop⟩,
    val := n
  }

-- the Node macro doesn't seem to like these...
--TODO(Sebastian): these should probably generate better error messages
def parseBinLit : BasicParserM Unit :=
ch '0' *> (ch 'b' <|> ch 'B') *> many1' (ch '0' <|> ch '1')

def parseOctLit : BasicParserM String :=
ch '0' *> (ch 'o' <|> ch 'O') *> takeWhile1 (λ c, c ≥ '0' && c < '8')

def parseHexLit : BasicParserM String :=
ch '0' *> (ch 'x' <|> ch 'X') *> takeWhile1 (λ c, c.isDigit || c.isAlpha)

--TODO(Sebastian): other bases
def number' : basicParser :=
nodeLongestChoice! number {
  base10: raw $ takeWhile1 Char.isDigit,
  base2:  raw parseBinLit,
  base8:  raw parseOctLit,
  base16: raw parseHexLit,
}

def stringLit' : basicParser :=
node! stringLit [val: raw parseStringLiteral]

private def mkConsumeToken (tk : TokenConfig) (it : String.OldIterator) : basicParser :=
let it' := it.nextn tk.prefix.length in
MonadParsec.lift $ λ _, Parsec.Result.ok (mkRawRes it it') it' none

def numberOrStringLit : basicParser :=
number' <|> stringLit'

def tokenCont (it : String.OldIterator) (tk : TokenConfig) : basicParser :=
do id ← ident',
   it' ← leftOver,
   -- if a token is both a symbol and a valid identifier (i.e. a keyword),
   -- we want it to be recognized as a symbol
   if it.offset + tk.prefix.length ≥ it'.offset then
      mkConsumeToken tk it
   else pure id

def token : basicParser :=
do it ← leftOver,
   cache ← getCache,
   -- NOTE: using `catch` instead of `<|>` so that error messages from the second block are preferred
   catch (do
     -- check token cache
     some tkc ← pure cache.tokenCache | failure,
     guard (it.offset = tkc.startIt.offset),
     -- hackishly update Parsec Position
     MonadParsec.lift (λ it, Parsec.Result.ok () tkc.stopIt none),
     putCache {cache with hit := cache.hit + 1},
     pure tkc.tk
   ) (λ _, do
     -- cache failed, update cache

     identStart ← observing $ lookahead (satisfy isIdFirst <|> ch idBeginEscape),
     tk ← matchToken,
     tk ← match tk, identStart with
     | some tk@{suffixParser := some _, ..}, _ :=
       error "token: not implemented" --str tk *> MonadParsec.lift r
     | some tk, Except.ok _    := tokenCont it tk
     | some tk, Except.error _ := mkConsumeToken tk it
     | none, Except.ok _       := ident'
     | none, Except.error _    := numberOrStringLit,
     tk ← withTrailing tk,
     newIt ← leftOver,
     putCache {cache with tokenCache := some ⟨it, newIt, tk⟩, miss := cache.miss + 1},
     pure tk
   )

def peekToken : BasicParserM (Except (Parsec.Message Syntax) Syntax) :=
observing (try (lookahead token))

variable [monadBasicParser m]

def symbolCore (sym : String) (lbp : Nat) (ex : DList String) : Parser :=
lift $ try $ do {
  it ← leftOver,
  stx@(Syntax.atom ⟨_, sym'⟩) ← token | error "" ex it,
  when (sym ≠ sym') $
    error sym' ex it,
  pure stx
} <?> sym

@[inline] def symbol (sym : String) (lbp := 0) : Parser :=
let sym := sym.trim in
symbolCore sym lbp (DList.singleton sym)

instance symbol.tokens (sym lbp) : Parser.HasTokens (symbol sym lbp : Parser) :=
⟨[⟨sym.trim, lbp, none⟩]⟩
instance symbol.View (sym lbp) : Parser.HasView (Option SyntaxAtom) (symbol sym lbp : Parser) :=
{ view := λ stx, match stx with
  | Syntax.atom atom := some atom
  | _                := none,
  review := λ a, (Syntax.atom <$> a).getOrElse Syntax.missing }
instance symbol.viewDefault (sym lbp) : Parser.HasViewDefault (symbol sym lbp : Parser) _
  (some {info := none, val := sym.trim}) := ⟨⟩

def number.Parser : Parser :=
lift $ try $ do {
  it ← leftOver,
  stx ← token,
  if stx.isOfKind number then pure stx
  else error "" (DList.singleton "number") it
}

instance number.Parser.tokens : Parser.HasTokens (number.Parser : Parser) := default _
instance number.Parser.view : Parser.HasView number.View (number.Parser : Parser) :=
{..number.HasView}

private def toNatCore (base : Nat) : String.OldIterator → Nat → Nat → Nat
| it      0     r := r
| it      (i+1) r :=
  let c := it.curr in
  let val := if c.isDigit then
    c.toNat - '0'.toNat
  else if c ≥ 'a' ∧ c ≤ 'f' then
    c.toNat - 'a'.toNat
  else
    c.toNat - 'A'.toNat in
  let r := r*base + val in
  toNatCore it.next i r

private def toNatBase (s : String) (base : Nat) : Nat :=
toNatCore base s.mkOldIterator s.length 0

def number.View.toNat : number.View → Nat
| (number.View.base10 (some atom)) := atom.val.toNat
| (number.View.base2  (some atom)) := toNatBase atom.val 2
| (number.View.base8  (some atom)) := toNatBase atom.val 8
| (number.View.base16 (some atom)) := toNatBase atom.val 16
| _ := 1138 -- should never happen, but let's still choose a grep-able number

def number.View.ofNat (n : Nat) : number.View :=
number.View.base10 (some {val := toString n})

def stringLit.Parser : Parser :=
lift $ try $ do {
  it ← leftOver,
  stx ← token,
  some _ ← pure $ tryView stringLit stx | error "" (DList.singleton "String") it,
  pure stx
} <?> "String"

instance stringLit.Parser.tokens : Parser.HasTokens (stringLit.Parser : Parser) := default _
instance stringLit.Parser.View : Parser.HasView stringLit.View (stringLit.Parser : Parser) :=
{..stringLit.HasView}

def stringLit.View.value (lit : stringLit.View) : Option String := do
  atom ← lit.val,
  Except.ok s ← pure $ Parsec.parse (parseStringLiteral : Parsec' _) atom.val
    | failure,
  pure s

def ident.Parser : Parser :=
lift $ try $ do {
  it ← leftOver,
  stx@(Syntax.ident _) ← token | error "" (DList.singleton "identifier") it,
  pure stx
} <?> "identifier"

instance ident.Parser.tokens : Parser.HasTokens (ident.Parser : Parser) := default _
instance ident.Parser.View : Parser.HasView SyntaxIdent (ident.Parser : Parser) :=
{ view := λ stx, match stx with
    | Syntax.ident id := id
    | _               := {rawVal := Substring.ofString "NOTAnIdent", val := `NOTAnIdent},
  review := Syntax.ident }

/-- Read identifier without consulting the token table. -/
def rawIdent.Parser : Parser :=
lift $ ident' >>= withTrailing

instance rawIdent.Parser.tokens : Parser.HasTokens (rawIdent.Parser : Parser) := default _
instance rawIdent.Parser.View : Parser.HasView SyntaxIdent (rawIdent.Parser : Parser) :=
{..(ident.Parser.View : HasView _ (_ : Parser))}

/-- Check if the following token is the symbol _or_ identifier `sym`. Useful for
    parsing local tokens that have not been added to the token table (but may have
    been so by some unrelated code).

    For example, the universe `max` Function is parsed using this Combinator so that
    it can still be used as an identifier outside of universes (but registering it
    as a token in a Term Syntax would not break the universe Parser). -/
def symbolOrIdent (sym : String) : Parser :=
lift $ try $ do
  it ← leftOver,
  stx ← token,
  let sym' := match stx with
  | Syntax.atom ⟨_, sym'⟩ := some sym'
  | Syntax.ident id := some id.rawVal.toString
  | _ := none,
  when (sym' ≠ some sym) $
    error "" (DList.singleton (repr sym)) it,
  pure stx

instance symbolOrIdent.tokens (sym) : Parser.HasTokens (symbolOrIdent sym : Parser) :=
default _
instance symbolOrIdent.View (sym) : Parser.HasView Syntax (symbolOrIdent sym : Parser) := default _

/-- A unicode symbol with an ASCII fallback -/
@[derive HasTokens HasView]
def unicodeSymbol (unicode ascii : String) (lbp := 0) : Parser :=
lift $ anyOf [symbol unicode lbp, symbol ascii lbp]
-- use unicode variant by default
instance unicodeSymbol.viewDefault (u a lbp) : Parser.HasViewDefault (unicodeSymbol u a lbp : Parser) _ (Syntax.atom ⟨none, u⟩) := ⟨⟩

def indexed {α : Type} (map : TokenMap α) : m (List α) :=
lift $ do
  Except.ok tk ← peekToken | error "",
  n ← match tk with
  | Syntax.atom ⟨_, s⟩ := pure $ mkSimpleName s
  | Syntax.ident _ := pure `ident
  | Syntax.rawNode n := pure n.kind.name
  | _ := error "",
  Option.toMonad $ map.find n

end «Parser»
end Lean
