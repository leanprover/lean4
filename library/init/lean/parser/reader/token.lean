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
open lean.parser.monad_parser
open string

def match_token : reader (option token_config) :=
do st ← get,
   it ← left_over,
   -- the slowest longest prefix matcher on Earth
   pure $ st.tokens.foldl (λ acc tk,
     if tk.prefix.mk_iterator.is_prefix_of_remaining it then
       match acc with
       | some tk' := if tk.prefix > tk'.prefix then tk else tk'
       | none     := tk
     else acc) none

private def finish_comment_block_aux : nat → nat → reader unit
| nesting (n+1) :=
  str "/-" *> finish_comment_block_aux (nesting + 1) n <|>
  str "-/" *>
    (if nesting = 1 then pure ()
     else finish_comment_block_aux (nesting - 1) n) <|>
  any *> finish_comment_block_aux nesting n
| _ _ := error

def finish_comment_block (nesting := 1) : reader unit :=
remaining >>= finish_comment_block_aux nesting

private def whitespace_aux : nat → reader unit
| (n+1) :=
do start ← pos,
   tk ← whitespace *> match_token,
   (match tk with
    | some ⟨"--", _⟩    := str "--" *> take_while' (= '\n') *> whitespace_aux n
    | some ⟨"/-", _⟩    := str "/-" *> finish_comment_block *> whitespace_aux n
    | _                 := pure ())
| 0 := error

/-- Skip whitespace and comments. -/
--TODO(Sebastian): store whitespace prefix and suffix in syntax objects
def whitespace : reader unit :=
-- every `whitespace_aux` loop reads at least one char
do r ← remaining,
   whitespace_aux r

/-- Match a string literally without consulting the token table. -/
def raw_symbol (sym : string) : reader syntax :=
do start ← pos,
   try (whitespace *> str sym),
   stop ← pos,
   pure $ syntax.atom ⟨some ⟨start, stop⟩, atomic_val.string sym⟩

--TODO(Sebastian): other bases
private def number' (start : position) : reader syntax :=
do num ← take_while1 char.is_digit,
   stop ← pos,
   pure $ syntax.node ⟨`base10_lit, [syntax.atom ⟨some ⟨start, stop⟩, atomic_val.string num⟩]⟩

private def ident' (start : position) : reader syntax :=
do n ← identifier,
   stop ← pos,
   pure $ syntax.ident ⟨some ⟨start, stop⟩, n, none, none⟩

def token : reader syntax :=
do start ← pos,
   tk ← whitespace *> match_token,
   match tk with
   -- constant-length token
   | some ⟨tk, none⟩   :=
     do str tk,
        stop ← pos,
        pure $ syntax.atom ⟨some ⟨start, stop⟩, atomic_val.string tk⟩
   -- variable-length token
   | some ⟨tk, some r⟩ := str tk *> monad_parser.lift (r start)
   | none              := number' start <|> ident' start

--TODO(Sebastian): error messages
def symbol (sym : string) : reader syntax := try $
do stx@(syntax.atom ⟨_, atomic_val.string sym'⟩) ← token | error "" (dlist.singleton sym),
   when (sym ≠ sym') $
     error "" (dlist.singleton sym),
   pure stx

def keyword (kw : string) : reader syntax := symbol kw

def number : reader syntax := try $
do stx@(syntax.node ⟨`base10_lit, _⟩) ← token | error,
   pure stx

def ident : reader syntax := try $
do stx@(syntax.ident _) ← token | error,
   pure stx

end reader
end lean.parser
