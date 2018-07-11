/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Tokenizer for the Lean language

Even though our reader architecture does not statically depend on a tokenizer but works directly on
the input string, we still use a "tokenizer" parser in the Lean reader in some circumstances:
* to distinguish between identifiers and keywords
* for error recovery: advance until next command token
* ...?
-/

prelude
import init.lean.parser.reader.basic init.util

namespace lean.parser
namespace reader
open lean.parser.monad_parsec
open string

def match_token : read_m (option token_config) :=
do st ← get,
   it ← left_over,
   -- the slowest longest prefix matcher on Earth
   pure $ st.tokens.foldl (λ acc tk,
     if tk.prefix.mk_iterator.is_prefix_of_remaining it then
       match acc with
       | some tk' := if tk.prefix > tk'.prefix then tk else tk'
       | none     := tk
     else acc) none

private def finish_comment_block_aux : nat → nat → read_m unit
| nesting (n+1) :=
  str "/-" *> finish_comment_block_aux (nesting + 1) n <|>
  str "-/" *>
    (if nesting = 1 then pure ()
     else finish_comment_block_aux (nesting - 1) n) <|>
  any *> finish_comment_block_aux nesting n
| _ _ := error "unreachable"

def finish_comment_block (nesting := 1) : read_m unit :=
do r ← remaining,
   finish_comment_block_aux nesting (r+1) <?> "end of comment block"

private def whitespace_aux : nat → read_m unit
| (n+1) :=
do tk ← whitespace *> match_token,
   (match tk with
    | some ⟨"--", _⟩    := str "--" *> take_while' (= '\n') *> whitespace_aux n
    | some ⟨"/-", _⟩    := str "/-" *> finish_comment_block *> whitespace_aux n
    | _                 := pure ())
| 0 := error "unreachable"

/-- Skip whitespace and comments. -/
def whitespace : read_m substring :=
-- every `whitespace_aux` loop reads at least one char
do start ← left_over,
   whitespace_aux (start.remaining+1),
   stop ← left_over,
   pure ⟨start, stop⟩

def with_source_info {α : Type} (r : read_m α) : read_m (α × source_info) :=
do leading ← whitespace,
   p ← pos,
   a ← r,
   -- TODO(Sebastian): less greedy, more natural whitespace assignement
   -- E.g. only read up to the next line break
   trailing ← whitespace,
   pure (a, ⟨leading, p, trailing⟩)

/-- Match a string literally without consulting the token table. -/
def raw_symbol (sym : string) : reader :=
{ tokens := [], -- no additional tokens
  read := try $ do
    (_, info) ← with_source_info $ str sym,
    pure $ syntax.atom ⟨info, atomic_val.string sym⟩ }

--TODO(Sebastian): other bases
private def number' : read_m (source_info → syntax) :=
do num ← take_while1 char.is_digit,
   pure $ λ i, syntax.node ⟨`base10_lit, [syntax.atom ⟨i, atomic_val.string num⟩]⟩

private def ident' : read_m (source_info → syntax) :=
do n ← identifier,
   pure $ λ i, syntax.ident ⟨i, n, none, none⟩

def token : read_m syntax :=
do (r, i) ← with_source_info $ do {
     tk ← match_token,
     match tk with
     -- constant-length token
     | some ⟨tk, none⟩   :=
       do str tk,
          pure $ λ i, syntax.atom ⟨some i, atomic_val.string tk⟩
     -- variable-length token
     | some ⟨tk, some r⟩ := str tk *> monad_parsec.lift r
     | none              := number' <|> ident'
   },
   pure (r i)

--TODO(Sebastian): error messages
def symbol (sym : string) : reader :=
{ tokens := [⟨sym, none⟩],
  read := try $ do
    stx@(syntax.atom ⟨_, atomic_val.string sym'⟩) ← token | error "" (dlist.singleton sym),
    when (sym ≠ sym') $
      error "" (dlist.singleton sym),
    pure stx }

def keyword (kw : string) : reader := symbol kw

def number : reader :=
{ read := try $ do
    stx@(syntax.node ⟨`base10_lit, _⟩) ← token | error,
    pure stx }

def ident : reader :=
{ read := try $ do
    stx@(syntax.ident _) ← token | error,
    pure stx }

end reader
end lean.parser
