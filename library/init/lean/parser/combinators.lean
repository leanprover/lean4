/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Syntax-tree creating parser combinators
-/
prelude
import init.lean.parser.basic
import init.data.list.instances

namespace lean
namespace parser

namespace combinators
open has_tokens has_view monad_parsec

variables {α : Type} {m : Type → Type}
local notation `parser` := m syntax
variables [monad m] [monad_except (parsec.message syntax) m] [monad_parsec syntax m] [alternative m]

def node (k : syntax_node_kind) (rs : list parser) : parser :=
do args ← rs.mfoldl (λ (p : list syntax) r, do
     args ← pure p,
     -- on error, append partial syntax tree to previous successful parses and rethrow
     a ← catch r $ λ msg, match args with
       -- do not wrap an error in the first argument to uphold the invariant documented at `syntax_node`
       | [] := throw msg
       | _  :=
         let args := msg.custom.get :: args in
         throw {msg with custom := syntax.node ⟨k, args.reverse⟩},
     pure (a::args)
   ) [],
   pure $ syntax.node ⟨k, args.reverse⟩

@[reducible] def seq : list parser → parser := node no_kind

instance node.tokens (k) (rs : list parser) [parser.has_tokens rs] : parser.has_tokens (node k rs) :=
⟨tokens rs⟩

instance node.view (k) (rs : list parser) [i : has_view α k] : parser.has_view α (node k rs) :=
{ view := i.view, review := i.review }

-- Each parser combinator comes equipped with `has_view` and `has_tokens` instances

private def many1_aux (p : parser) : list syntax → nat → parser
| as 0     := error "unreachable"
| as (n+1) := do
  a ← catch p (λ msg, throw {msg with custom :=
    -- append `syntax.missing` to make clear that list is incomplete
    syntax.node ⟨no_kind, (syntax.missing::msg.custom.get::as).reverse⟩}),
  many1_aux (a::as) n <|> pure (syntax.node ⟨no_kind, (a::as).reverse⟩)

def many1 (r : parser) : parser :=
do rem ← remaining, many1_aux r [] (rem+1)

instance many1.tokens (r : parser) [parser.has_tokens r] : parser.has_tokens (many1 r) :=
⟨tokens r⟩

instance many1.view (r : parser) [parser.has_view α r] : parser.has_view (list α) (many1 r) :=
{ view := λ stx, match stx with
    | syntax.node ⟨@no_kind, stxs⟩ := stxs.map (has_view.view r)
    | _ := [has_view.view r syntax.missing],
  review := λ as, syntax.node ⟨no_kind, as.map (review r)⟩ }

def many (r : parser) : parser :=
many1 r <|> pure (syntax.node ⟨no_kind, []⟩)

instance many.tokens (r : parser) [parser.has_tokens r] : parser.has_tokens (many r) :=
⟨tokens r⟩

instance many.view (r : parser) [has_view α r] : parser.has_view (list α) (many r) :=
/- Remark: `many1.view` can handle empty list. -/
{..many1.view r}

private def sep_by_aux (p : m syntax) (sep : parser) (allow_trailing_sep : bool) : bool → list syntax → nat → parser
| p_opt as 0     := error "unreachable"
| p_opt as (n+1) := do
  let p := if p_opt then some <$> p <|> pure none else some <$> p,
  some a ← catch p (λ msg, throw {msg with custom :=
    -- append `syntax.missing` to make clear that list is incomplete
    syntax.node ⟨no_kind, (syntax.missing::msg.custom.get::as).reverse⟩})
    | pure (syntax.node ⟨no_kind, as.reverse⟩),
  -- I don't want to think about what the output on a failed separator parse should look like
  let sep := try sep,
  some s ← some <$> sep <|> pure none
    | pure (syntax.node ⟨no_kind, (a::as).reverse⟩),
  sep_by_aux allow_trailing_sep (s::a::as) n

def sep_by (p sep : parser) (allow_trailing_sep := tt) : parser :=
do rem ← remaining, sep_by_aux p sep allow_trailing_sep tt [] (rem+1)

def sep_by1 (p sep : parser) (allow_trailing_sep := tt) : parser :=
do rem ← remaining, sep_by_aux p sep allow_trailing_sep ff [] (rem+1)

instance sep_by.tokens (p sep : parser) (a) [parser.has_tokens p] [parser.has_tokens sep] :
  parser.has_tokens (sep_by p sep a) :=
⟨tokens p ++ tokens sep⟩

private def sep_by.view_aux {α β} (p sep : parser) [parser.has_view α p] [parser.has_view β sep] :
  list syntax → list (α × option β)
| []    := []
| [stx] := [(has_view.view p stx, none)]
| (stx1::stx2::stxs) := (has_view.view p stx1, some $ has_view.view sep stx2)::sep_by.view_aux stxs

instance sep_by.view {α β} (p sep : parser) (a) [parser.has_view α p] [parser.has_view β sep] :
  parser.has_view (list (α × option β)) (sep_by p sep a) :=
{ view := λ stx, match stx with
    | syntax.node ⟨@no_kind, stxs⟩ := sep_by.view_aux p sep stxs
    | _ := failure,
  review := λ as, syntax.node ⟨no_kind, as.bind (λ a, match a with
    | ⟨v, some vsep⟩ := [review p v, review sep vsep]
    | ⟨v, none⟩      := [review p v])⟩ }

instance sep_by1.tokens (p sep : parser) (a) [parser.has_tokens p] [parser.has_tokens sep] :
  parser.has_tokens (sep_by1 p sep a) :=
⟨tokens (sep_by p sep a)⟩

instance sep_by1.view {α β} (p sep : parser) (a) [parser.has_view α p] [parser.has_view β sep] :
  parser.has_view (list (α × option β)) (sep_by1 p sep a) :=
{..sep_by.view p sep a}

def optional (r : parser) : parser :=
do r ← optional $
     -- on error, wrap in "some"
     catch r (λ msg, throw {msg with custom := syntax.node ⟨no_kind, [msg.custom.get]⟩}),
   pure $ match r with
   | some r := syntax.node ⟨no_kind, [r]⟩
   | none   := syntax.node ⟨no_kind, []⟩

instance optional.tokens (r : parser) [parser.has_tokens r] : parser.has_tokens (optional r) :=
⟨tokens r⟩
instance optional.view (r : parser) [parser.has_view α r] : parser.has_view (option α) (optional r) :=
{ view := λ stx, match stx with
    | syntax.node ⟨no_kind, []⟩ := none
    | syntax.node ⟨no_kind, [stx]⟩ := some $ has_view.view r stx
    | _ := some $ has_view.view r syntax.missing,
  review := λ a, match a with
    | some a := syntax.node ⟨no_kind, [review r a]⟩
    | none   := syntax.node ⟨no_kind, []⟩ }
instance optional.view_default (r : parser) [parser.has_view α r] : parser.has_view_default (optional r) (option α) none := ⟨⟩

/-- Parse a list `[p1, ..., pn]` of parsers as `p1 <|> ... <|> pn`.
    Note that there is NO explicit encoding of which parser was chosen;
    parsers should instead produce distinct node names for disambiguation. -/
def any_of (rs : list parser) : parser :=
match rs with
| [] := error "any_of"
| (r::rs) := rs.foldl (<|>) r

instance any_of.tokens (rs : list parser) [parser.has_tokens rs] : parser.has_tokens (any_of rs) :=
⟨tokens rs⟩
instance any_of.view (rs : list parser) : parser.has_view syntax (any_of rs) := default _

/-- Parse a list `[p1, ..., pn]` of parsers with `monad_parsec.longest_match`.
    If the result is ambiguous, wrap it in a `choice` node.
    Note that there is NO explicit encoding of which parser was chosen;
    parsers should instead produce distinct node names for disambiguation. -/
def longest_match (rs : list parser) : parser :=
do stxs ← monad_parsec.longest_match rs,
   match stxs with
   | [stx] := pure stx
   | _     := pure $ syntax.node ⟨choice, stxs⟩

instance longest_match.tokens (rs : list parser) [parser.has_tokens rs] : parser.has_tokens (longest_match rs) :=
⟨tokens rs⟩
instance longest_match.view (rs : list parser) : parser.has_view syntax (longest_match rs) := default _

/-- Parse a list `[p1, ..., pn]` of parsers as `p1 <|> ... <|> pn`.
    The result will be wrapped in a node with the the index of the successful
    parser as the name. -/
def choice_aux : list parser → nat → parser
| []      _ := error "choice: empty list"
| (r::rs) i :=
  do { stx ← r,
       pure $ syntax.node ⟨⟨name.mk_numeral name.anonymous i⟩, [stx]⟩ }
  <|> choice_aux rs (i+1)

def choice (rs : list parser) : parser :=
choice_aux rs 0

instance choice.tokens (rs : list parser) [parser.has_tokens rs] : parser.has_tokens (choice rs) :=
⟨tokens rs⟩

/- Remark: `choice` does not have `has_view` instance because we only use it at the pratt combinator
   which doesn't need the view. -/

instance try.tokens (r : parser) [parser.has_tokens r] : parser.has_tokens (try r) :=
⟨tokens r⟩
instance try.view (r : parser) [i : parser.has_view α r] : parser.has_view α (try r) :=
{..i}

instance label.tokens (r : parser) (l) [parser.has_tokens r] : parser.has_tokens (label r l) :=
⟨tokens r⟩
instance label.view (r : parser) (l) [i : parser.has_view α r] : parser.has_view α (label r l) :=
{..i}

instance dbg.tokens (r : parser) (l) [parser.has_tokens r] : parser.has_tokens (dbg l r) :=
⟨tokens r⟩
instance dbg.view (r  : parser) (l) [i : parser.has_view α r] : parser.has_view α (dbg l r) :=
{..i}

instance recurse.tokens (α δ m a) [monad_rec α δ m] : parser.has_tokens (recurse a : m δ) :=
default _ -- recursive use should not contribute any new tokens
instance recurse.view (α δ m a) [monad_rec α δ m] : parser.has_view syntax (recurse a : m δ) := default _

instance monad_lift.tokens {m' : Type → Type} [has_monad_lift_t m m'] (r : m syntax) [parser.has_tokens r] :
  parser.has_tokens (monad_lift r : m' syntax) :=
⟨tokens r⟩
instance monad_lift.view {m' : Type → Type} [has_monad_lift_t m m'] (r : m syntax) [i : parser.has_view α r] :
  parser.has_view α (monad_lift r : m' syntax) :=
{..i}

instance seq_left.tokens {α : Type} (x : m α) (p : m syntax) [parser.has_tokens p] : parser.has_tokens (p <* x) :=
⟨tokens p⟩
instance seq_left.view {α β : Type} (x : m α) (p : m syntax) [i : parser.has_view β p] : parser.has_view β (p <* x) :=
{..i}

instance seq_right.tokens {α : Type} (x : m α) (p : m syntax) [parser.has_tokens p] : parser.has_tokens (x *> p) :=
⟨tokens p⟩
instance seq_right.view {α β : Type} (x : m α) (p : m syntax) [i : parser.has_view β p] : parser.has_view β (x *> p) :=
{..i}

instance coe.tokens {β} (r : parser) [parser.has_tokens r] [has_coe_t parser β]: parser.has_tokens (coe r : β) :=
⟨tokens r⟩
instance coe.view {β} (r : parser) [i : parser.has_view α r] [has_coe_t parser β] : parser.has_view α (coe r : β) :=
{..i}

end combinators
end parser
end lean
