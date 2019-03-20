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
open hasTokens hasView monadParsec

variables {α : Type} {m : Type → Type}
local notation `parser` := m syntax
variables [monad m] [monadExcept (parsec.message syntax) m] [monadParsec syntax m] [alternative m]

def node (k : syntaxNodeKind) (rs : list parser) : parser :=
do args ← rs.mfoldl (λ (args : list syntax) r, do
     -- on error, append partial syntax tree to previous successful parses and rethrow
     a ← catch r $ λ msg, match args with
       -- do not wrap an error in the first argument to uphold the invariant documented at `syntaxNode`
       | [] := throw msg
       | _  :=
         let args := msg.custom.get :: args in
         throw {msg with custom := syntax.mkNode k args.reverse},
     pure (a::args)
   ) [],
   pure $ syntax.mkNode k args.reverse

@[reducible] def seq : list parser → parser := node noKind

instance node.tokens (k) (rs : list parser) [parser.hasTokens rs] : parser.hasTokens (node k rs) :=
⟨tokens rs⟩

instance node.view (k) (rs : list parser) [i : hasView α k] : parser.hasView α (node k rs) :=
{ view := i.view, review := i.review }

-- Each parser combinator comes equipped with `hasView` and `hasTokens` instances

private def many1Aux (p : parser) : list syntax → nat → parser
| as 0     := error "unreachable"
| as (n+1) := do
  a ← catch p (λ msg, throw {msg with custom :=
    -- append `syntax.missing` to make clear that list is incomplete
    syntax.list (syntax.missing::msg.custom.get::as).reverse}),
  many1Aux (a::as) n <|> pure (syntax.list (a::as).reverse)

def many1 (r : parser) : parser :=
do rem ← remaining, many1Aux r [] (rem+1)

instance many1.tokens (r : parser) [parser.hasTokens r] : parser.hasTokens (many1 r) :=
⟨tokens r⟩

instance many1.view (r : parser) [parser.hasView α r] : parser.hasView (list α) (many1 r) :=
{ view := λ stx, match stx.asNode with
    | some n := n.args.map (hasView.view r)
    | _ := [hasView.view r syntax.missing],
  review := λ as, syntax.list $ as.map (review r) }

def many (r : parser) : parser :=
many1 r <|> pure (syntax.list [])

instance many.tokens (r : parser) [parser.hasTokens r] : parser.hasTokens (many r) :=
⟨tokens r⟩

instance many.view (r : parser) [hasView α r] : parser.hasView (list α) (many r) :=
/- Remark: `many1.view` can handle empty list. -/
{..many1.view r}

private def sepByAux (p : m syntax) (sep : parser) (allowTrailingSep : bool) : bool → list syntax → nat → parser
| pOpt as 0     := error "unreachable"
| pOpt as (n+1) := do
  let p := if pOpt then some <$> p <|> pure none else some <$> p,
  some a ← catch p (λ msg, throw {msg with custom :=
    -- append `syntax.missing` to make clear that list is incomplete
    syntax.list (syntax.missing::msg.custom.get::as).reverse})
    | pure (syntax.list as.reverse),
  -- I don't want to think about what the output on a failed separator parse should look like
  let sep := try sep,
  some s ← some <$> sep <|> pure none
    | pure (syntax.list (a::as).reverse),
  sepByAux allowTrailingSep (s::a::as) n

def sepBy (p sep : parser) (allowTrailingSep := tt) : parser :=
do rem ← remaining, sepByAux p sep allowTrailingSep tt [] (rem+1)

def sepBy1 (p sep : parser) (allowTrailingSep := tt) : parser :=
do rem ← remaining, sepByAux p sep allowTrailingSep ff [] (rem+1)

instance sepBy.tokens (p sep : parser) (a) [parser.hasTokens p] [parser.hasTokens sep] :
  parser.hasTokens (sepBy p sep a) :=
⟨tokens p ++ tokens sep⟩

structure sepBy.elem.view (α β : Type) :=
(item      : α)
(separator : option β := none)

instance sepBy.elem.view.itemCoe {α β : Type} : hasCoeT α (sepBy.elem.view α β) :=
⟨λ a, ⟨a, none⟩⟩

private def sepBy.viewAux {α β} (p sep : parser) [parser.hasView α p] [parser.hasView β sep] :
  list syntax → list (sepBy.elem.view α β)
| []    := []
| [stx] := [⟨hasView.view p stx, none⟩]
| (stx1::stx2::stxs) := ⟨hasView.view p stx1, some $ hasView.view sep stx2⟩::sepBy.viewAux stxs

instance sepBy.view {α β} (p sep : parser) (a) [parser.hasView α p] [parser.hasView β sep] :
  parser.hasView (list (sepBy.elem.view α β)) (sepBy p sep a) :=
{ view := λ stx, match stx.asNode with
    | some n := sepBy.viewAux p sep n.args
    | _ := [⟨view p syntax.missing, none⟩],
  review := λ as, syntax.list $ as.bind (λ a, match a with
    | ⟨v, some vsep⟩ := [review p v, review sep vsep]
    | ⟨v, none⟩      := [review p v]) }

instance sepBy1.tokens (p sep : parser) (a) [parser.hasTokens p] [parser.hasTokens sep] :
  parser.hasTokens (sepBy1 p sep a) :=
⟨tokens (sepBy p sep a)⟩

instance sepBy1.view {α β} (p sep : parser) (a) [parser.hasView α p] [parser.hasView β sep] :
  parser.hasView (list (sepBy.elem.view α β)) (sepBy1 p sep a) :=
{..sepBy.view p sep a}

def optional (r : parser) : parser :=
do r ← optional $
     -- on error, wrap in "some"
     catch r (λ msg, throw {msg with custom := syntax.list [msg.custom.get]}),
   pure $ match r with
   | some r := syntax.list [r]
   | none   := syntax.list []

instance optional.tokens (r : parser) [parser.hasTokens r] : parser.hasTokens (optional r) :=
⟨tokens r⟩
instance optional.view (r : parser) [parser.hasView α r] : parser.hasView (option α) (optional r) :=
{ view := λ stx, match stx.asNode with
    | some {args := [], ..} := none
    | some {args := [stx], ..} := some $ hasView.view r stx
    | _ := some $ view r syntax.missing,
  review := λ a, match a with
    | some a := syntax.list [review r a]
    | none   := syntax.list [] }
instance optional.viewDefault (r : parser) [parser.hasView α r] : parser.hasViewDefault (optional r) (option α) none := ⟨⟩

/-- Parse a list `[p1, ..., pn]` of parsers as `p1 <|> ... <|> pn`.
    Note that there is NO explicit encoding of which parser was chosen;
    parsers should instead produce distinct node names for disambiguation. -/
def anyOf (rs : list parser) : parser :=
match rs with
| [] := error "anyOf"
| (r::rs) := rs.foldl (<|>) r

instance anyOf.tokens (rs : list parser) [parser.hasTokens rs] : parser.hasTokens (anyOf rs) :=
⟨tokens rs⟩
instance anyOf.view (rs : list parser) : parser.hasView syntax (anyOf rs) := default _

/-- Parse a list `[p1, ..., pn]` of parsers with `monadParsec.longestMatch`.
    If the result is ambiguous, wrap it in a `choice` node.
    Note that there is NO explicit encoding of which parser was chosen;
    parsers should instead produce distinct node names for disambiguation. -/
def longestMatch (rs : list parser) : parser :=
do stxs ← monadParsec.longestMatch rs,
   match stxs with
   | [stx] := pure stx
   | _     := pure $ syntax.mkNode choice stxs

instance longestMatch.tokens (rs : list parser) [parser.hasTokens rs] : parser.hasTokens (longestMatch rs) :=
⟨tokens rs⟩
instance longestMatch.view (rs : list parser) : parser.hasView syntax (longestMatch rs) := default _

def choiceAux : list parser → nat → parser
| []      _ := error "choice: empty list"
| (r::rs) i :=
  do { stx ← r,
       pure $ syntax.mkNode ⟨name.mkNumeral name.anonymous i⟩ [stx] }
  <|> choiceAux rs (i+1)

/-- Parse a list `[p1, ..., pn]` of parsers as `p1 <|> ... <|> pn`.
    The result will be wrapped in a node with the index of the successful
    parser as the name.

    Remark: Does not have a `hasView` instance because we only use it in `nodeChoice!` macros
    that define their own views. -/
def choice (rs : list parser) : parser :=
choiceAux rs 0

instance choice.tokens (rs : list parser) [parser.hasTokens rs] : parser.hasTokens (choice rs) :=
⟨tokens rs⟩

/-- Like `choice`, but using `longestMatch`. Does not create choice nodes, prefers the first successful parser. -/
def longestChoice (rs : list parser) : parser :=
do stx::stxs ← monadParsec.longestMatch $ rs.enum.map $ λ ⟨i, r⟩, do {
     stx ← r,
     pure $ syntax.mkNode ⟨name.mkNumeral name.anonymous i⟩ [stx]
   } | error "unreachable",
   pure stx

instance longestChoice.tokens (rs : list parser) [parser.hasTokens rs] : parser.hasTokens (longestChoice rs) :=

⟨tokens rs⟩
instance try.tokens (r : parser) [parser.hasTokens r] : parser.hasTokens (try r) :=
⟨tokens r⟩
instance try.view (r : parser) [i : parser.hasView α r] : parser.hasView α (try r) :=
{..i}

instance label.tokens (r : parser) (l) [parser.hasTokens r] : parser.hasTokens (label r l) :=
⟨tokens r⟩
instance label.view (r : parser) (l) [i : parser.hasView α r] : parser.hasView α (label r l) :=
{..i}

instance recurse.tokens (α δ m a) [monadRec α δ m] : parser.hasTokens (recurse a : m δ) :=
default _ -- recursive use should not contribute any new tokens
instance recurse.view (α δ m a) [monadRec α δ m] : parser.hasView syntax (recurse a : m δ) := default _

instance monadLift.tokens {m' : Type → Type} [hasMonadLiftT m m'] (r : m syntax) [parser.hasTokens r] :
  parser.hasTokens (monadLift r : m' syntax) :=
⟨tokens r⟩
instance monadLift.view {m' : Type → Type} [hasMonadLiftT m m'] (r : m syntax) [i : parser.hasView α r] :
  parser.hasView α (monadLift r : m' syntax) :=
{..i}

instance seqLeft.tokens {α : Type} (x : m α) (p : m syntax) [parser.hasTokens p] : parser.hasTokens (p <* x) :=
⟨tokens p⟩
instance seqLeft.view {α β : Type} (x : m α) (p : m syntax) [i : parser.hasView β p] : parser.hasView β (p <* x) :=
{..i}

instance seqRight.tokens {α : Type} (x : m α) (p : m syntax) [parser.hasTokens p] : parser.hasTokens (x *> p) :=
⟨tokens p⟩
instance seqRight.view {α β : Type} (x : m α) (p : m syntax) [i : parser.hasView β p] : parser.hasView β (x *> p) :=
{..i}

instance coe.tokens {β} (r : parser) [parser.hasTokens r] [hasCoeT parser β]: parser.hasTokens (coe r : β) :=
⟨tokens r⟩
instance coe.view {β} (r : parser) [i : parser.hasView α r] [hasCoeT parser β] : parser.hasView α (coe r : β) :=
{..i}
instance coe.viewDefault {β} (d : α) (r : parser) [hasView α r] [parser.hasViewDefault r α d] [hasCoeT parser β] : parser.hasViewDefault (coe r : β) α d := ⟨⟩

end combinators
end parser
end lean
