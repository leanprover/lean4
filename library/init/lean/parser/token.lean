/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Tokenizer for the Lean language

Even though our parser architecture does not statically depend on a tokenizer but works directly on
the input string, we still use a "tokenizer" parser in the Lean parser in some circumstances:
* to distinguish between identifiers and keywords
* for error recovery: advance until next command token
* ...?
-/

prelude
import init.lean.parser.combinators init.lean.parser.stringLiteral

namespace lean
namespace parser
open monadParsec combinators string hasView

def matchToken : basicParserM (option tokenConfig) :=
do cfg ← read,
   it ← leftOver,
   pure $ prod.snd <$> cfg.tokens.matchPrefix it

private def finishCommentBlockAux : nat → nat → basicParserM unit
| nesting (n+1) :=
  str "/-" *> finishCommentBlockAux (nesting + 1) n
  <|>
  str "-/" *> (if nesting = 1 then pure () else finishCommentBlockAux (nesting - 1) n)
  <|>
  any *> finishCommentBlockAux nesting n
| _ _ := error "unreachable"

def finishCommentBlock (nesting := 1) : basicParserM unit :=
do r ← remaining,
   finishCommentBlockAux nesting (r+1) <?> "end of comment block"

private def whitespaceAux : nat → basicParserM unit
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
local notation `parser` := m syntax
local notation `lift` := @monadLift basicParserM _ _ _

/-- Skip whitespace and comments. -/
def whitespace : basicParserM unit :=
hidden $ do
  start ← leftOver,
  -- every `whitespaceAux` loop reads at least one char
  whitespaceAux (start.remaining+1)

section
variables [monad m] [monadParsec syntax m]

@[inline] def asSubstring {α : Type} (p : m α) : m substring :=
do start ← leftOver,
   p,
   stop ← leftOver,
   pure ⟨start, stop⟩

variables [monadBasicParser m]

private mutual def updateTrailing, updateTrailingLst
with updateTrailing : substring → syntax → syntax
| trailing (syntax.atom a@⟨some info, _⟩) := syntax.atom {a with info := some {info with trailing := trailing}}
| trailing (syntax.ident id@{info := some info, ..}) := syntax.ident {id with info := some {info with trailing := trailing}}
| trailing (syntax.rawNode n) := syntax.rawNode {n with args := updateTrailingLst trailing n.args}
| trailing stx := stx
with updateTrailingLst : substring → list syntax → list syntax
| trailing [] := []
| trailing [stx] := [updateTrailing trailing stx]
| trailing (stx::stxs) := stx :: updateTrailingLst trailing stxs

def withTrailing (stx : syntax) : m syntax :=
do -- TODO(Sebastian): less greedy, more natural whitespace assignment
   -- E.g. only read up to the next line break
   trailing ← lift $ asSubstring $ whitespace,
   pure $ updateTrailing trailing stx

def mkRawRes (start stop : string.iterator) : syntax :=
let ss : substring := ⟨start, stop⟩ in
syntax.atom ⟨some {leading := ⟨start, start⟩, pos := start.offset, trailing := ⟨stop, stop⟩}, ss.toString⟩

/-- Match an arbitrary parser and return the consumed string in a `syntax.atom`. -/
@[inline] def raw {α : Type} (p : m α) (trailingWs := ff) : parser := do
  start ← leftOver,
  p,
  stop ← leftOver,
  let stx := mkRawRes start stop,
  if trailingWs then withTrailing stx else pure stx

instance raw.tokens {α} (p : m α) (t) : parser.hasTokens (raw p t : parser) := default _
instance raw.view {α} (p : m α) (t) : parser.hasView (option syntaxAtom) (raw p t : parser) :=
{ view := λ stx, match stx with
  | syntax.atom atom := some atom
  | _                := none,
  review := λ a, (syntax.atom <$> a).getOrElse syntax.missing }

/-- Like `raw (str s)`, but default to `s` in views. -/
@[inline, derive hasTokens hasView]
def rawStr (s : string) (trailingWs := ff) : parser :=
raw (str s) trailingWs

instance rawStr.viewDefault (s) (t) : parser.hasViewDefault (rawStr s t : parser) (option syntaxAtom) (some {val := s}) :=
⟨⟩

end

setOption class.instanceMaxDepth 200

@[derive hasTokens hasView]
def detailIdentPart.parser : basicParserM syntax :=
nodeChoice! detailIdentPart {
  escaped: node! detailIdentPartEscaped [
    escBegin: rawStr idBeginEscape.toString,
    escaped: raw $ takeUntil1 isIdEndEscape,
    escEnd: rawStr idEndEscape.toString,
  ],
  default: raw $ satisfy isIdFirst *> takeWhile isIdRest
}

@[derive hasTokens hasView]
def detailIdentSuffix.parser : recT unit syntax basicParserM syntax :=
-- consume '.' only when followed by a character starting an detailIdentPart
try (lookahead (ch '.' *> (ch idBeginEscape <|> satisfy isIdFirst)))
*> node! detailIdentSuffix [«.»: rawStr ".", ident: recurse ()]

def detailIdent' : recT unit syntax basicParserM syntax :=
node! detailIdent [part: monadLift detailIdentPart.parser, suffix: optional detailIdentSuffix.parser]

/-- A parser that gives a more detailed view of `syntaxIdent.rawVal`. Not used by default for
    performance reasons. -/
def detailIdent.parser : basicParserM syntax :=
recT.runParsec detailIdent' $ λ _, detailIdent'

private def ident' : basicParser :=
do
  start ← leftOver,
  s  ← idPart,
  n ← foldl name.mkString (mkSimpleName s) $ do {
    -- consume '.' only when followed by a character starting an detailIdentPart
    try (lookahead (ch '.' *> (ch idBeginEscape <|> satisfy isIdFirst))),
    ch '.',
    idPart
  },
  stop ← leftOver,
  pure $ syntax.ident {
    info := some {leading := ⟨start, start⟩, pos := start.offset, trailing := ⟨stop, stop⟩},
    rawVal := ⟨start, stop⟩,
    val := n
  }

-- the node macro doesn't seem to like these...
--TODO(Sebastian): these should probably generate better error messages
def parseBinLit : basicParserM unit :=
ch '0' *> (ch 'b' <|> ch 'B') *> many1' (ch '0' <|> ch '1')

def parseOctLit : basicParserM string :=
ch '0' *> (ch 'o' <|> ch 'O') *> takeWhile1 (λ c, c ≥ '0' && c < '8')

def parseHexLit : basicParserM string :=
ch '0' *> (ch 'x' <|> ch 'X') *> takeWhile1 (λ c, c.isDigit || c.isAlpha)

--TODO(Sebastian): other bases
def number' : basicParser :=
nodeLongestChoice! number {
  base10: raw $ takeWhile1 char.isDigit,
  base2:  raw parseBinLit,
  base8:  raw parseOctLit,
  base16: raw parseHexLit,
}

def stringLit' : basicParser :=
node! stringLit [val: raw parseStringLiteral]

private def mkConsumeToken (tk : tokenConfig) (it : string.iterator) : basicParser :=
let it' := it.nextn tk.prefix.length in
monadParsec.lift $ λ _, parsec.result.ok (mkRawRes it it') it' none

def numberOrStringLit : basicParser :=
number' <|> stringLit'

def tokenCont (it : string.iterator) (tk : tokenConfig) : basicParser :=
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
     -- hackishly update parsec position
     monadParsec.lift (λ it, parsec.result.ok () tkc.stopIt none),
     putCache {cache with hit := cache.hit + 1},
     pure tkc.tk
   ) (λ _, do
     -- cache failed, update cache

     identStart ← observing $ lookahead (satisfy isIdFirst <|> ch idBeginEscape),
     tk ← matchToken,
     tk ← match tk, identStart with
     | some tk@{suffixParser := some _, ..}, _ :=
       error "token: not implemented" --str tk *> monadParsec.lift r
     | some tk, except.ok _    := tokenCont it tk
     | some tk, except.error _ := mkConsumeToken tk it
     | none, except.ok _       := ident'
     | none, except.error _    := numberOrStringLit,
     tk ← withTrailing tk,
     newIt ← leftOver,
     putCache {cache with tokenCache := some ⟨it, newIt, tk⟩, miss := cache.miss + 1},
     pure tk
   )

def peekToken : basicParserM (except (parsec.message syntax) syntax) :=
observing (try (lookahead token))

variable [monadBasicParser m]

def symbolCore (sym : string) (lbp : nat) (ex : dlist string) : parser :=
lift $ try $ do {
  it ← leftOver,
  stx@(syntax.atom ⟨_, sym'⟩) ← token | error "" ex it,
  when (sym ≠ sym') $
    error sym' ex it,
  pure stx
} <?> sym

@[inline] def symbol (sym : string) (lbp := 0) : parser :=
let sym := sym.trim in
symbolCore sym lbp (dlist.singleton sym)

instance symbol.tokens (sym lbp) : parser.hasTokens (symbol sym lbp : parser) :=
⟨[⟨sym.trim, lbp, none⟩]⟩
instance symbol.view (sym lbp) : parser.hasView (option syntaxAtom) (symbol sym lbp : parser) :=
{ view := λ stx, match stx with
  | syntax.atom atom := some atom
  | _                := none,
  review := λ a, (syntax.atom <$> a).getOrElse syntax.missing }
instance symbol.viewDefault (sym lbp) : parser.hasViewDefault (symbol sym lbp : parser) _
  (some {info := none, val := sym.trim}) := ⟨⟩

def number.parser : parser :=
lift $ try $ do {
  it ← leftOver,
  stx ← token,
  some _ ← pure $ tryView number stx | error "" (dlist.singleton "number") it,
  pure stx
} <?> "number"

instance number.parser.tokens : parser.hasTokens (number.parser : parser) := default _
instance number.parser.view : parser.hasView number.view (number.parser : parser) :=
{..number.hasView}

private def toNatCore (base : nat) : string.iterator → nat → nat → nat
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

private def toNatBase (s : string) (base : nat) : nat :=
toNatCore base s.mkIterator s.length 0

def number.view.toNat : number.view → nat
| (number.view.base10 (some atom)) := atom.val.toNat
| (number.view.base2  (some atom)) := toNatBase atom.val 2
| (number.view.base8  (some atom)) := toNatBase atom.val 8
| (number.view.base16 (some atom)) := toNatBase atom.val 16
| _ := 1138 -- should never happen, but let's still choose a grep-able number

def number.view.ofNat (n : nat) : number.view :=
number.view.base10 (some {val := toString n})

def stringLit.parser : parser :=
lift $ try $ do {
  it ← leftOver,
  stx ← token,
  some _ ← pure $ tryView stringLit stx | error "" (dlist.singleton "string") it,
  pure stx
} <?> "string"

instance stringLit.parser.tokens : parser.hasTokens (stringLit.parser : parser) := default _
instance stringLit.parser.view : parser.hasView stringLit.view (stringLit.parser : parser) :=
{..stringLit.hasView}

def stringLit.view.value (lit : stringLit.view) : option string := do
  atom ← lit.val,
  except.ok s ← pure $ parsec.parse (parseStringLiteral : parsec' _) atom.val
    | failure,
  pure s

def ident.parser : parser :=
lift $ try $ do {
  it ← leftOver,
  stx@(syntax.ident _) ← token | error "" (dlist.singleton "identifier") it,
  pure stx
} <?> "identifier"

instance ident.parser.tokens : parser.hasTokens (ident.parser : parser) := default _
instance ident.parser.view : parser.hasView syntaxIdent (ident.parser : parser) :=
{ view := λ stx, match stx with
    | syntax.ident id := id
    | _               := {rawVal := substring.ofString "NOTAnIdent", val := `NOTAnIdent},
  review := syntax.ident }

/-- Read identifier without consulting the token table. -/
def rawIdent.parser : parser :=
lift $ ident' >>= withTrailing

instance rawIdent.parser.tokens : parser.hasTokens (rawIdent.parser : parser) := default _
instance rawIdent.parser.view : parser.hasView syntaxIdent (rawIdent.parser : parser) :=
{..(ident.parser.view : hasView _ (_ : parser))}

/-- Check if the following token is the symbol _or_ identifier `sym`. Useful for
    parsing local tokens that have not been added to the token table (but may have
    been so by some unrelated code).

    For example, the universe `max` function is parsed using this combinator so that
    it can still be used as an identifier outside of universes (but registering it
    as a token in a term syntax would not break the universe parser). -/
def symbolOrIdent (sym : string) : parser :=
lift $ try $ do
  it ← leftOver,
  stx ← token,
  let sym' := match stx with
  | syntax.atom ⟨_, sym'⟩ := some sym'
  | syntax.ident id := some id.rawVal.toString
  | _ := none,
  when (sym' ≠ some sym) $
    error "" (dlist.singleton (repr sym)) it,
  pure stx

instance symbolOrIdent.tokens (sym) : parser.hasTokens (symbolOrIdent sym : parser) :=
default _
instance symbolOrIdent.view (sym) : parser.hasView syntax (symbolOrIdent sym : parser) := default _

/-- A unicode symbol with an ASCII fallback -/
@[derive hasTokens hasView]
def unicodeSymbol (unicode ascii : string) (lbp := 0) : parser :=
lift $ anyOf [symbol unicode lbp, symbol ascii lbp]
-- use unicode variant by default
instance unicodeSymbol.viewDefault (u a lbp) : parser.hasViewDefault (unicodeSymbol u a lbp : parser) _ (syntax.atom ⟨none, u⟩) := ⟨⟩

def indexed {α : Type} (map : tokenMap α) : m (list α) :=
lift $ do
  except.ok tk ← peekToken | error "",
  n ← match tk with
  | syntax.atom ⟨_, s⟩ := pure $ mkSimpleName s
  | syntax.ident _ := pure `ident
  | syntax.rawNode n := pure n.kind.name
  | _ := error "",
  option.toMonad $ map.find n

end «parser»
end lean
