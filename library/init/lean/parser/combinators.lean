/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Syntax-tree creating parser combinators
-/
prelude
import init.lean.parser.basic

namespace lean
namespace parser

@[pattern] def choice := {syntax_node_kind . name := `lean.parser.choice}

namespace combinators
open has_tokens has_view monad_parsec

variables {α : Type} {m : Type → Type}
local notation `parser` := m syntax
variables [monad m] [monad_except (parsec.message syntax) m] [monad_parsec syntax m] [alternative m]

def node' (k : option syntax_node_kind) (rs : list parser) : parser :=
do (args, _) ← rs.mfoldl (λ (p : list syntax × nat) r, do
     (args, remaining) ← pure p,
     -- on error, append partial syntax tree and `missing` objects to previous successful parses and rethrow
     a ← catch r $ λ msg,
       let args := list.repeat syntax.missing (remaining-1) ++ msg.custom :: args in
       throw {msg with custom := syntax.node ⟨k, args.reverse⟩},
     pure (a::args, remaining - 1)
   ) ([], rs.length),
   pure $ syntax.node ⟨k, args.reverse⟩

@[reducible] def seq : list parser → parser := node' none
@[reducible] def node (k : syntax_node_kind) (α : Type) : list parser → parser := node' k

instance node'.tokens (k) (rs : list parser) [parser.has_tokens rs] : parser.has_tokens (node' k rs) :=
⟨tokens rs⟩

instance node.view (k) (α : Type) (rs : list parser) [i : tysyntax.is_view α] : parser.has_view (node k α rs) α :=
{ view := i.view, review := i.review }

private def many1_aux (p : parser) : list syntax → nat → parser
| as 0     := error "unreachable"
| as (n+1) := do
  a ← catch p (λ msg, throw {msg with custom :=
    -- append `syntax.missing` to make clear that list is incomplete
    syntax.node ⟨none, (syntax.missing::msg.custom::as).reverse⟩}),
  many1_aux (a::as) n <|> pure (syntax.node ⟨none, (a::as).reverse⟩)

def many1 (r : parser) : parser :=
do rem ← remaining, many1_aux r [] (rem+1)

instance many1.tokens (r : parser) [parser.has_tokens r] : parser.has_tokens (many1 r) :=
⟨tokens r⟩

instance list.is_view : tysyntax.is_view (list (tysyntax α)) :=
{ view := λ stx, match stx with
    | syntax.node ⟨none, stxs⟩ := pure stxs
    | _ := failure,
  review := λ as, syntax.node ⟨none, as⟩ }

instance many1.view (r : parser) [parser.has_view r α] : parser.has_view (many1 r) (list (tysyntax α)) :=
{..list.is_view}

def many (r : parser) : parser :=
many1 r <|> pure (syntax.node ⟨none, []⟩)

instance many.tokens (r : parser) [parser.has_tokens r] : parser.has_tokens (many r) :=
⟨tokens r⟩

instance many.view (r : parser) [has_view r α] : parser.has_view (many r) (list (tysyntax α)) :=
{..many1.view r}

private def sep_by_aux (p : m syntax) (sep : parser) (allow_trailing_sep : bool) : bool → list syntax → nat → parser
| p_opt as 0     := error "unreachable"
| p_opt as (n+1) := do
  let p := if p_opt then some <$> p <|> pure none else some <$> p,
  some a ← catch p (λ msg, throw {msg with custom :=
    -- append `syntax.missing` to make clear that list is incomplete
    syntax.node ⟨none, (syntax.missing::msg.custom::as).reverse⟩})
    | pure (syntax.node ⟨none, as.reverse⟩),
  -- I don't want to think about what the output on a failed separator parse should look like
  let sep := try sep,
  some s ← some <$> sep <|> pure none
    | pure (syntax.node ⟨none, (a::as).reverse⟩),
  sep_by_aux allow_trailing_sep (s::a::as) n

def sep_by (p sep : parser) (allow_trailing_sep := tt) : parser :=
do rem ← remaining, sep_by_aux p sep allow_trailing_sep tt [] (rem+1)

def sep_by1 (p sep : parser) (allow_trailing_sep := tt) : parser :=
do rem ← remaining, sep_by_aux p sep allow_trailing_sep ff [] (rem+1)

instance sep_by.tokens (p sep : parser) (a) [parser.has_tokens p] [parser.has_tokens sep] :
  parser.has_tokens (sep_by p sep a) :=
⟨tokens p ++ tokens sep⟩

private def sep_by.view_aux {α β} (p sep : parser) [parser.has_view p α] [parser.has_view sep β] :
  list syntax → option (list (α × option β))
| []    := some []
| [stx] := do
  vp ← view p stx,
  some [(vp, none)]
| (stx1::stx2::stxs) := do
  vp ← view p stx1,
  vsep ← view sep stx2,
  vs ← sep_by.view_aux stxs,
  some ((vp, some vsep)::vs)

instance sep_by.view {α β} (p sep : parser) (a) [parser.has_view p α] [parser.has_view sep β] :
  parser.has_view (sep_by p sep a) (list (α × option β)) :=
{ view := λ stx, match stx with
    | syntax.node ⟨none, stxs⟩ := sep_by.view_aux p sep stxs
    | _ := failure,
  review := λ as, syntax.node ⟨none, as.bind (λ a, match a with
    | ⟨v, some vsep⟩ := [review p v, review sep vsep]
    | ⟨v, none⟩      := [review p v])⟩ }

instance sep_by1.tokens (p sep : parser) (a) [parser.has_tokens p] [parser.has_tokens sep] :
  parser.has_tokens (sep_by1 p sep a) :=
⟨tokens (sep_by p sep a)⟩

instance sep_by1.view {α β} (p sep : parser) (a) [parser.has_view p α] [parser.has_view sep β] :
  parser.has_view (sep_by1 p sep a) (list (α × option β)) :=
{..sep_by.view p sep a}

def optional (r : parser) : parser :=
do r ← optional $
     -- on error, wrap in "some"
     catch r (λ msg, throw {msg with custom := syntax.node ⟨none, [msg.custom]⟩}),
   pure $ match r with
   | some r := syntax.node ⟨none, [r]⟩
   | none   := syntax.node ⟨none, []⟩

instance optional.tokens (r : parser) [parser.has_tokens r] : parser.has_tokens (optional r) :=
⟨tokens r⟩

instance optional.is_view : tysyntax.is_view (option (tysyntax α)) :=
{ view := λ stx, match stx with
    | syntax.missing := failure
    | syntax.node ⟨none, []⟩ := pure none
    | syntax.node ⟨none, [stx]⟩ := pure (some stx)
    | _ := failure,
  review := λ a, match a with
    | some a := syntax.node ⟨none, [a]⟩
    | none   := syntax.node ⟨none, []⟩ }

instance optional.view (r : parser) [parser.has_view r α] : parser.has_view (optional r) (option (tysyntax α)) :=
{..optional.is_view}

/-- Parse a list `[p1, ..., pn]` of parsers as `p1 <|> ... <|> pn`.
    Note that there is NO explicit encoding of which parser was chosen;
    parsers should instead produce distinct node names for disambiguation. -/
def any_of (rs : list parser) : parser :=
match rs with
| [] := error "any_of"
| (r::rs) := rs.foldl (<|>) r

instance any_of.tokens (rs : list parser) [parser.has_tokens rs] : parser.has_tokens (any_of rs) :=
⟨tokens rs⟩
instance any_of.view (rs : list parser) : parser.has_view (any_of rs) syntax := default _

/-- Parse a list `[p1, ..., pn]` of parsers with `monad_parsec.longest_match`.
    If the result is ambiguous, wrap it in a `choice` node.
    Note that there is NO explicit encoding of which parser was chosen;
    parsers should instead produce distinct node names for disambiguation. -/
def longest_match (rs : list parser) : parser :=
do stxs ← monad_parsec.longest_match rs,
   pure $ syntax.node ⟨choice, stxs⟩

instance longest_match.tokens (rs : list parser) [parser.has_tokens rs] : parser.has_tokens (longest_match rs) :=
⟨tokens rs⟩
instance longest_match.view (rs : list parser) : parser.has_view (longest_match rs) syntax := default _

/-- Parse a list `[p1, ..., pn]` of parsers as `p1 <|> ... <|> pn`.
    The result will be wrapped in a node with the the index of the successful
    parser as the name. -/
def choice (rs : list parser) : parser :=
rs.enum.foldr
  (λ ⟨i, r⟩ r', (λ stx, syntax.node ⟨some ⟨name.mk_numeral name.anonymous i⟩, [stx]⟩) <$> r <|> r')
  -- use `foldr` so that any other error is preferred over this one
  (error "choice: empty list")

instance choice.tokens (rs : list parser) [parser.has_tokens rs] : parser.has_tokens (choice rs) :=
⟨tokens rs⟩

instance try.tokens (r : parser) [parser.has_tokens r] : parser.has_tokens (try r) :=
⟨tokens r⟩
instance try.view (r : parser) [i : parser.has_view r α] : parser.has_view (try r) α :=
{..i}

instance label.tokens (r : parser) (l) [parser.has_tokens r] : parser.has_tokens (label r l) :=
⟨tokens r⟩
instance label.view (r : parser) (l) [i : parser.has_view r α] : parser.has_view (label r l) α :=
{..i}

instance dbg.tokens (r : parser) (l) [parser.has_tokens r] : parser.has_tokens (dbg l r) :=
⟨tokens r⟩
instance dbg.view (r  : parser) (l) [i : parser.has_view r α] : parser.has_view (dbg l r) α :=
{..i}

instance recurse.tokens (α δ m a) [monad_rec α δ m] : parser.has_tokens (recurse a : m δ) :=
default _ -- recursive use should not contribute any new tokens
instance recurse.view (α δ m a) [monad_rec α δ m] : parser.has_view (recurse a : m δ) syntax := default _

def with_recurse {α : Type} (init : α) (r : α → rec_t α syntax m syntax) : parser :=
rec_t.run (λ _, error "recursion limit") r init

instance with_recurse.tokens {α} (init : α) (r : α → _) [has_tokens (r init)] :
  parser.has_tokens (with_recurse init r : parser) :=
⟨tokens (r init)⟩
instance with_recurse.view {α β} (init : α) (r : α → _) [i : has_view (r init) β] :
  parser.has_view (with_recurse init r : parser) β :=
{..i}

instance monad_lift.tokens {m' : Type → Type} [has_monad_lift_t m m'] (r : m syntax) [parser.has_tokens r] :
  parser.has_tokens (monad_lift r : m' syntax) :=
⟨tokens r⟩
instance monad_lift.view {m' : Type → Type} [has_monad_lift_t m m'] (r : m syntax) [i : parser.has_view r α] :
  parser.has_view (monad_lift r : m' syntax) α :=
{..i}

instance seq_left.tokens {α : Type} (x : m α) (p : m syntax) [parser.has_tokens p] : parser.has_tokens (p <* x) :=
⟨tokens p⟩
instance seq_left.view {α β : Type} (x : m α) (p : m syntax) [i : parser.has_view p β] : parser.has_view (p <* x) β :=
{..i}

instance seq_right.tokens {α : Type} (x : m α) (p : m syntax) [parser.has_tokens p] : parser.has_tokens (x *> p) :=
⟨tokens p⟩
instance seq_right.view {α β : Type} (x : m α) (p : m syntax) [i : parser.has_view p β] : parser.has_view (x *> p) β :=
{..i}

instance coe.tokens {β} (r : parser) [parser.has_tokens r] [has_coe_t parser β]: parser.has_tokens (coe r : β) :=
⟨tokens r⟩
instance coe.view {β} (r : parser) [i : parser.has_view r α] [has_coe_t parser β] : parser.has_view (coe r : β) α :=
{..i}

end combinators
end parser
end lean
