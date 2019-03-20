/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich

Implementation for the parsec parser combinators described in the
paper:
https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/parsec-paper-letter.pdf
-/
prelude
import init.data.toString init.data.string.basic init.data.list.basic init.control.except
import init.data.repr init.lean.name init.data.dlist init.control.monadFail init.control.combinators

namespace lean
namespace parser
open string (iterator)

namespace parsec
@[reducible] def position : Type := nat

structure message (μ : Type := unit) :=
(it         : iterator)
(unexpected : string       := "")          -- unexpected input
(expected   : dlist string := dlist.empty) -- expected productions
(custom     : option μ)

def expected.toString : list string → string
| []       := ""
| [e]      := e
| [e1, e2] := e1 ++ " or " ++ e2
| (e::es)  := e ++ ", " ++ expected.toString es

def message.text {μ : Type} (msg : message μ) : string :=
let unexpected := (if msg.unexpected = "" then [] else ["unexpected " ++ msg.unexpected]) in
let exList := msg.expected.toList in
let expected := if exList = [] then [] else ["expected " ++ expected.toString exList] in
"\n".intercalate $ unexpected ++ expected


protected def message.toString {μ : Type} (msg : message μ) : string :=
let (line, col) := msg.it.toString.lineColumn msg.it.offset in
-- always print ":"; we assume at least one of `unexpected` and `expected` to be non-empty
"error at line " ++ toString line ++ ", column " ++ toString col ++ ":\n" ++ msg.text

instance {μ : Type} : hasToString (message μ) :=
⟨message.toString⟩

-- use for e.g. upcasting parsec errors with `monadExcept.liftExcept`
instance {μ : Type} : hasLift (message μ) string :=
⟨toString⟩

/-
Remark: we store expected "error" messages in `okEps` results.
They contain the error that would have occurred if a
successful "epsilon" alternative was not taken.
-/
inductive result (μ α : Type)
| ok {} (a : α) (it : iterator) (expected : option $ dlist string) : result
| error {} (msg : message μ) (consumed : bool)                     : result

@[inline] def result.mkEps {μ α : Type} (a : α) (it : iterator) : result μ α :=
result.ok a it (some dlist.empty)
end parsec

open parsec

def parsecT (μ : Type) (m : Type → Type) (α : Type) :=
iterator → m (result μ α)

abbrev parsec (μ : Type) := parsecT μ id
/-- `parsec` without custom error message type -/
abbrev parsec' := parsec unit

namespace parsecT
open parsec.result
variables {m : Type → Type} [monad m] {μ α β : Type}

def run (p : parsecT μ m α) (s : string) (fname := "") : m (except (message μ) α) :=
do r ← p s.mkIterator,
   pure $ match r with
   | ok a _ _     := except.ok a
   | error msg _  := except.error msg

def runFrom (p : parsecT μ m α) (it : iterator) (fname := "") : m (except (message μ) α) :=
do r ← p it,
   pure $ match r with
   | ok a _ _     := except.ok a
   | error msg _  := except.error msg

@[inline] protected def pure (a : α) : parsecT μ m α :=
λ it, pure (mkEps a it)

def eps : parsecT μ m unit :=
parsecT.pure ()

protected def failure : parsecT μ m α :=
λ it, pure (error { unexpected := "failure", it := it, custom := none } ff)

def merge (msg₁ msg₂ : message μ) : message μ :=
{ expected := msg₁.expected ++ msg₂.expected, ..msg₁ }

@[inlineIfReduce] def bindMkRes (ex₁ : option (dlist string)) (r : result μ β) : result μ β :=
match ex₁, r with
| none,     ok b it _          := ok b it none
| none,     error msg _        := error msg tt
| some ex₁, ok b it (some ex₂) := ok b it (some $ ex₁ ++ ex₂)
| some ex₁, error msg₂ ff      := error { expected := ex₁ ++ msg₂.expected, .. msg₂ } ff
| some ex₁, other              := other

/--
  The `bind p q` combinator behaves as follows:
  1- If `p` fails, then it fails.
  2- If `p` succeeds and consumes input, then execute `q`
  3- If `q` succeeds but does not consume input, then execute `q`
     and merge error messages if both do not consume any input.
-/
@[inline] protected def bind (p : parsecT μ m α) (q : α → parsecT μ m β) : parsecT μ m β :=
λ it, do
 r ← p it,
 match r with
 | ok a it ex₁  := bindMkRes ex₁ <$> q a it
 | error msg c  := pure (error msg c)

/-- More efficient `bind` that does not correctly merge `expected` and `consumed` information. -/
@[inline] def bind' (p : parsecT μ m α) (q : α → parsecT μ m β) : parsecT μ m β :=
λ it, do
 r ← p it,
 match r with
 | ok a it ex₁  := q a it
 | error msg c  := pure (error msg c)

instance : monad (parsecT μ m) :=
{ bind := λ _ _, parsecT.bind, pure := λ _, parsecT.pure }

/-- `monad` instance using `bind'`. -/
def monad' : monad (parsecT μ m) :=
{ bind := λ _ _, parsecT.bind', pure := λ _, parsecT.pure }

instance : monadFail parsec' :=
{ fail := λ _ s it, error { unexpected := s, it := it, custom := () } ff }

instance : monadExcept (message μ) (parsecT μ m) :=
{ throw := λ _ msg it, pure (error msg ff),
  catch := λ _ p c it, do
    r ← p it,
    match r with
    | error msg cns := do {
      r ← c msg msg.it,
      pure $ match r with
      | error msg' cns' := error msg' (cns || cns')
      | other := other }
    | other       := pure other }

instance : hasMonadLift m (parsecT μ m) :=
{ monadLift := λ α x it, do a ← x, pure (mkEps a it) }

def expect (msg : message μ) (exp : string) : message μ :=
{expected := dlist.singleton exp, ..msg}

@[inlineIfReduce] def labelsMkRes (r : result μ α) (lbls : dlist string) : result μ α :=
match r with
  | ok a it (some _) := ok a it (some lbls)
  | error msg ff     := error {expected := lbls, ..msg} ff
  | other            := other

@[inline] def labels (p : parsecT μ m α) (lbls : dlist string) : parsecT μ m α :=
λ it, do
  r ← p it,
  pure $ labelsMkRes r lbls

@[inlineIfReduce] def tryMkRes (r : result μ α) : result μ α :=
match r with
| error msg _  := error msg ff
| other        := other

/--
`try p` behaves like `p`, but it pretends `p` hasn't
consumed any input when `p` fails.

It is useful for implementing infinite lookahead.
The parser `try p <|> q` will try `q` even when
`p` has consumed input.

It is also useful for specifying both the lexer and parser
together.
```
    (do try (ch 'l' >> ch 'e' >> ch 't'), whitespace, ...)
    <|>
    ...
```
Without the `try` combinator we will not be able to backtrack on the `let` keyword.
-/
@[inline] def try (p : parsecT μ m α) : parsecT μ m α :=
λ it, do
  r ← p it,
  pure $ tryMkRes r

@[inlineIfReduce] def orelseMkRes (msg₁ : message μ) (r : result μ α) : result μ α :=
match r with
| ok a it' (some ex₂) := ok a it' (some $ msg₁.expected ++ ex₂)
| error msg₂ ff       := error (merge msg₁ msg₂) ff
| other               := other

/--
  The `orelse p q` combinator behaves as follows:
  1- If `p` succeeds *or* consumes input, return
     its result. Otherwise, execute `q` and return its
     result.
     Recall that the `try p` combinator can be used to
     pretend that `p` did not consume any input, and
     simulate infinite lookahead.
  2- If both `p` and `q` did not consume any input, then
     combine their error messages (even if one of
     them succeeded).
-/
@[inline] protected def orelse (p q : parsecT μ m α) : parsecT μ m α :=
λ it, do
  r ← p it,
  match r with
  | error msg₁ ff := do { r ← q it, pure $ orelseMkRes msg₁ r }
  | other         := pure other

instance : alternative (parsecT μ m) :=
{ orelse         := λ _, parsecT.orelse,
  failure        := λ _, parsecT.failure,
  ..parsecT.monad }

/-- Run `p`, but do not consume any input when `p` succeeds. -/
@[specialize] def lookahead (p : parsecT μ m α) : parsecT μ m α :=
λ it, do
  r ← p it,
  pure $ match r with
  | ok a s' _ := mkEps a it
  | other     := other
end parsecT

/- Type class for abstracting from concrete monad stacks containing a `parsec` somewhere. -/
class monadParsec (μ : outParam Type) (m : Type → Type) :=
-- analogous to e.g. `monadReader.lift` before simplification (see there)
(lift {} {α : Type} : parsec μ α → m α)
-- Analogous to e.g. `monadReaderAdapter.map` before simplification (see there).
-- Its usage seems to be way too common to justify moving it into a separate type class.
(map {} {α : Type} : (∀ {m'} [monad m'] {α}, parsecT μ m' α → parsecT μ m' α) → m α → m α)

/-- `parsec` without custom error message type -/
abbrev monadParsec' := monadParsec unit

variables {μ : Type}

instance {m : Type → Type} [monad m] : monadParsec μ (parsecT μ m) :=
{ lift := λ α p it, pure (p it),
  map  := λ α f x, f x }

instance monadParsecTrans {m n : Type → Type} [hasMonadLift m n] [monadFunctor m m n n] [monadParsec μ m] : monadParsec μ n :=
{ lift := λ α p, monadLift (monadParsec.lift p : m α),
  map  := λ α f x, monadMap (λ β x, (monadParsec.map @f x : m β)) x }

namespace monadParsec
open parsecT
variables {m : Type → Type} [monad m] [monadParsec μ m] {α β : Type}

def error {α : Type} (unexpected : string) (expected : dlist string := dlist.empty)
          (it : option iterator := none) (custom : option μ := none) : m α :=
lift $ λ it', result.error { unexpected := unexpected, expected := expected, it := it.getOrElse it', custom := custom } ff

@[inline] def leftOver : m iterator :=
lift $ λ it, result.mkEps it it

/-- Return the number of characters left to be parsed. -/
@[inline] def remaining : m nat :=
string.iterator.remaining <$> leftOver

@[inline] def labels (p : m α) (lbls : dlist string) : m α :=
map (λ m' inst β p, @parsecT.labels m' inst μ β p lbls) p

@[inline] def label (p : m α) (lbl : string) : m α :=
labels p (dlist.singleton lbl)

infixr ` <?> `:2 := label

@[inline] def hidden (p : m α) : m α :=
labels p dlist.empty

/--
`try p` behaves like `p`, but it pretends `p` hasn't
consumed any input when `p` fails.

It is useful for implementing infinite lookahead.
The parser `try p <|> q` will try `q` even when
`p` has consumed input.

It is also useful for specifying both the lexer and parser
together.
```
    (do try (ch 'l' >> ch 'e' >> ch 't'), whitespace, ...)
    <|>
    ...
```
Without the `try` combinator we will not be able to backtrack on the `let` keyword.
-/

@[inline] def try (p : m α) : m α :=
map (λ m' inst β p, @parsecT.try m' inst μ β p) p

/-- Parse `p` without consuming any input. -/
@[inline] def lookahead (p : m α) : m α :=
map (λ m' inst β p, @parsecT.lookahead m' inst μ β p) p

/-- Faster version of `notFollowedBy (satisfy p)` -/
@[inline] def notFollowedBySat (p : char → bool) : m unit :=
do it ← leftOver,
   if !it.hasNext then pure ()
   else let c := it.curr in
       if p c then error (repr c)
       else pure ()

def eoiError (it : iterator) : result μ α :=
result.error { it := it, unexpected := "end of input", custom := default _ } ff

def curr : m char :=
string.iterator.curr <$> leftOver

@[inline] def cond (p : char → bool) (t : m α) (e : m α) : m α :=
mcond (p <$> curr) t e

/--
If the next character `c` satisfies `p`, then
update position and return `c`. Otherwise,
generate error message with current position and character. -/
@[inline] def satisfy (p : char → bool) : m char :=
do it ← leftOver,
   if !it.hasNext then error "end of input"
   else let c := it.curr in
       if p c then lift $ λ _, result.ok c it.next none
       else error (repr c)

def ch (c : char) : m char :=
satisfy (= c)

def alpha : m char :=
satisfy char.isAlpha

def digit : m char :=
satisfy char.isDigit

def upper : m char :=
satisfy char.isUpper

def lower : m char :=
satisfy char.isLower

def any : m char :=
satisfy (λ _, true)

private def strAux : nat → iterator → iterator → option iterator
| 0     _    it := some it
| (n+1) sIt it :=
  if it.hasNext ∧ sIt.curr = it.curr then strAux n sIt.next it.next
  else none

/--
`str s` parses a sequence of elements that match `s`. Returns the parsed string (i.e. `s`).
This parser consumes no input if it fails (even if a partial match).
Note: The behaviour of this parser is different to that the `string` parser in the ParsecT Μ M Haskell library,
as this one is all-or-nothing.
-/
def strCore (s : string) (ex : dlist string) : m string :=
if s.isEmpty then pure ""
else lift $ λ it, match strAux s.length s.mkIterator it with
  | some it' := result.ok s it' none
  | none     := result.error { it := it, expected := ex, custom := none } ff

@[inline] def str (s : string) : m string :=
strCore s (dlist.singleton (repr s))

private def takeAux : nat → string → iterator → result μ string
| 0     r it := result.ok r it none
| (n+1) r it :=
  if !it.hasNext then eoiError it
  else takeAux n (r.push (it.curr)) it.next

/-- Consume `n` characters. -/
def take (n : nat) : m string :=
if n = 0 then pure ""
else lift $ takeAux n ""

private def mkStringResult (r : string) (it : iterator) : result μ string :=
if r.isEmpty then result.mkEps r it
else result.ok r it none

@[specialize]
private def takeWhileAux (p : char → bool) : nat → string → iterator → result μ string
| 0     r it := mkStringResult r it
| (n+1) r it :=
  if !it.hasNext then mkStringResult r it
  else let c := it.curr in
       if p c then takeWhileAux n (r.push c) it.next
       else mkStringResult r it

/--
Consume input as long as the predicate returns `tt`, and return the consumed input.
This parser does not fail. It will return an empty string if the predicate
returns `ff` on the current character. -/
@[specialize] def takeWhile (p : char → bool) : m string :=
lift $ λ it, takeWhileAux p it.remaining "" it

@[specialize] def takeWhileCont (p : char → bool) (ini : string) : m string :=
lift $ λ it, takeWhileAux p it.remaining ini it

/--
Consume input as long as the predicate returns `tt`, and return the consumed input.
This parser requires the predicate to succeed on at least once. -/
@[specialize] def takeWhile1 (p : char → bool) : m string :=
do c ← satisfy p,
   takeWhileCont p (toString c)

/--
Consume input as long as the predicate returns `ff` (i.e. until it returns `tt`), and return the consumed input.
This parser does not fail. -/
@[inline] def takeUntil (p : char → bool) : m string :=
takeWhile (λ c, !p c)

@[inline] def takeUntil1 (p : char → bool) : m string :=
takeWhile1 (λ c, !p c)

private def mkConsumedResult (consumed : bool) (it : iterator) : result μ unit :=
if consumed then result.ok () it none
else result.mkEps () it

@[specialize] private def takeWhileAux' (p : char → bool) : nat → bool → iterator → result μ unit
| 0     consumed it := mkConsumedResult consumed it
| (n+1) consumed it :=
  if !it.hasNext then mkConsumedResult consumed it
  else let c := it.curr in
       if p c then takeWhileAux' n tt it.next
       else mkConsumedResult consumed it

/-- Similar to `takeWhile` but it does not return the consumed input. -/
@[specialize] def takeWhile' (p : char → bool) : m unit :=
lift $ λ it, takeWhileAux' p it.remaining ff it

/-- Similar to `takeWhile1` but it does not return the consumed input. -/
@[specialize] def takeWhile1' (p : char → bool) : m unit :=
satisfy p *> takeWhile' p

/-- Consume zero or more whitespaces. -/
@[noinline] def whitespace : m unit :=
takeWhile' char.isWhitespace

/-- Shorthand for `p <* whitespace` -/
@[inline] def lexeme (p : m α) : m α :=
p <* whitespace

/-- Parse a numeral in decimal. -/
@[noinline] def num : m nat :=
string.toNat <$> (takeWhile1 char.isDigit)

/-- Succeed only if there are at least `n` characters left. -/
def ensure (n : nat) : m unit :=
do it ← leftOver,
   if n ≤ it.remaining then pure ()
   else error "end of input" (dlist.singleton ("at least " ++ toString n ++ " characters"))

/-- Return the current position. -/
def pos : m position :=
string.iterator.offset <$> leftOver


/-- `notFollowedBy p` succeeds when parser `p` fails -/
@[inline] def notFollowedBy [monadExcept (message μ) m] (p : m α) (msg : string := "input") : m unit :=
do it ← leftOver,
   b ← lookahead $ catch (p *> pure ff) (λ _, pure tt),
   if b then pure () else error msg dlist.empty it

def eoi : m unit :=
do it ← leftOver,
   if it.remaining = 0 then pure ()
   else error (repr it.curr) (dlist.singleton ("end of input"))

@[specialize] def many1Aux [alternative m] (p : m α) : nat → m (list α)
| 0     := do a ← p, pure [a]
| (n+1) := do a ← p,
              as ← (many1Aux n <|> pure []),
              pure (a::as)

@[specialize] def many1 [alternative m] (p : m α) : m (list α) :=
do r ← remaining, many1Aux p r

@[specialize] def many [alternative m] (p : m α) : m (list α) :=
many1 p <|> pure []

@[specialize] def many1Aux' [alternative m] (p : m α) : nat → m unit
| 0     := p *> pure ()
| (n+1) := p *> (many1Aux' n <|> pure ())

@[inline] def many1' [alternative m] (p : m α) : m unit :=
do r ← remaining, many1Aux' p r

@[specialize] def many' [alternative m] (p : m α) : m unit :=
many1' p <|> pure ()

@[specialize] def sepBy1 [alternative m] (p : m α) (sep : m β) : m (list α) :=
(::) <$> p <*> many (sep *> p)

@[specialize] def sepBy [alternative m] (p : m α) (sep : m β) : m (list α) :=
sepBy1 p sep <|> pure []

@[specialize] def fixAux [alternative m] (f : m α → m α) : nat → m α
| 0     := error "fixAux: no progress"
| (n+1) := f (fixAux n)

@[specialize] def fix [alternative m] (f : m α → m α) : m α :=
do n ← remaining, fixAux f (n+1)

@[specialize] def foldrAux [alternative m] (f : α → β → β) (p : m α) (b : β) : nat → m β
| 0     := pure b
| (n+1) := (f <$> p <*> foldrAux n) <|> pure b

/-- Matches zero or more occurrences of `p`, and folds the result. -/
@[specialize] def foldr [alternative m] (f : α → β → β) (p : m α) (b : β) : m β :=
do it ← leftOver,
   foldrAux f p b it.remaining

@[specialize] def foldlAux [alternative m] (f : α → β → α) (p : m β) : α → nat → m α
| a 0     := pure a
| a (n+1) := (do x ← p, foldlAux (f a x) n) <|> pure a

/-- Matches zero or more occurrences of `p`, and folds the result. -/
@[specialize] def foldl [alternative m] (f : α → β → α) (a : α) (p : m β) : m α :=
do it ← leftOver,
   foldlAux f p a it.remaining

def unexpected (msg : string) : m α :=
error msg

def unexpectedAt (msg : string) (it : iterator) : m α :=
error msg dlist.empty it

/- Execute all parsers in `ps` and return the result of the longest parse(s) if any,
   or else the result of the furthest error. If there are two parses of
   equal length, the first parse wins. -/
@[specialize]
def longestMatch [monadExcept (message μ) m] (ps : list (m α)) : m (list α) :=
do it ← leftOver,
   r ← ps.mfoldr (λ p (r : result μ (list α)),
     lookahead $ catch
       (do
         a ← p,
         it ← leftOver,
         pure $ match r with
         | result.ok as it' none := if it'.offset > it.offset then r
             else if it.offset > it'.offset then result.ok [a] it none
             else result.ok (a::as) it none
         | _                     := result.ok [a] it none)
       (λ msg, pure $ match r with
           | result.error msg' _ := if msg'.it.offset > msg.it.offset then r
             else if msg.it.offset > msg'.it.offset then result.error msg tt
             else result.error (merge msg msg') (msg.it.offset > it.offset)
           | _ := r))
    ((error "longestMatch: empty list" : parsec _ _) it),
    lift $ λ _, r

@[specialize]
def observing [monadExcept (message μ) m] (p : m α) : m (except (message μ) α) :=
catch (except.ok <$> p) $ λ msg, pure (except.error msg)

end monadParsec

namespace monadParsec
open parsecT
variables {m : Type → Type} [monad m] [monadParsec unit m] {α β : Type}

end monadParsec

namespace parsecT
open monadParsec
variables {m : Type → Type} [monad m] {α β : Type}

def parse (p : parsecT μ m α) (s : string) (fname := "") : m (except (message μ) α) :=
run p s fname

def parseWithEoi (p : parsecT μ m α) (s : string) (fname := "") : m (except (message μ) α) :=
run (p <* eoi) s fname

def parseWithLeftOver (p : parsecT μ m α) (s : string) (fname := "") : m (except (message μ) (α × iterator)) :=
run (prod.mk <$> p <*> leftOver) s fname

end parsecT

def parsec.parse {α : Type} (p : parsec μ α) (s : string) (fname := "") : except (message μ) α :=
parsecT.parse p s fname

end parser
end lean
