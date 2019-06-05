/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Syntax-tree creating Parser Combinators
-/
prelude
import init.lean.parser.basic
import init.data.list.instances

namespace Lean
namespace Parser

namespace Combinators
open HasTokens HasView MonadParsec

variables {α : Type} {m : Type → Type}
local notation `Parser` := m Syntax
variables [Monad m] [MonadExcept (Parsec.Message Syntax) m] [MonadParsec Syntax m] [Alternative m]

def node (k : SyntaxNodeKind) (rs : List Parser) : Parser :=
do args ← rs.mfoldl (λ (args : List Syntax) r, do
     -- on error, append partial Syntax tree to previous successful parses and rethrow
     a ← catch r $ λ msg, match args with
       -- do not wrap an error in the first argument to uphold the invariant documented at `SyntaxNode`
       | [] := throw msg
       | _  :=
         let args := msg.custom.get :: args in
         throw {msg with custom := Syntax.mkNode k args.reverse},
     pure (a::args)
   ) [],
   pure $ Syntax.mkNode k args.reverse

@[reducible] def seq : List Parser → Parser := node noKind

instance node.tokens (k) (rs : List Parser) [Parser.HasTokens rs] : Parser.HasTokens (node k rs) :=
⟨tokens rs⟩

instance node.view (k) (rs : List Parser) [i : HasView α k] : Parser.HasView α (node k rs) :=
{ view := i.view, review := i.review }

-- Each Parser Combinator comes equipped with `HasView` and `HasTokens` instances

private def many1Aux (p : Parser) : List Syntax → Nat → Parser
| as 0     := error "unreachable"
| as (n+1) := do
  a ← catch p (λ msg, throw {msg with custom :=
    -- append `Syntax.missing` to make clear that List is incomplete
    Syntax.list (Syntax.missing::msg.custom.get::as).reverse}),
  many1Aux (a::as) n <|> pure (Syntax.list (a::as).reverse)

def many1 (r : Parser) : Parser :=
do rem ← remaining, many1Aux r [] (rem+1)

instance many1.tokens (r : Parser) [Parser.HasTokens r] : Parser.HasTokens (many1 r) :=
⟨tokens r⟩

instance many1.view (r : Parser) [Parser.HasView α r] : Parser.HasView (List α) (many1 r) :=
{ view := λ stx, match stx.asNode with
    | some n := n.args.map (HasView.view r)
    | _ := [HasView.view r Syntax.missing],
  review := λ as, Syntax.list $ as.map (review r) }

def many (r : Parser) : Parser :=
many1 r <|> pure (Syntax.list [])

instance many.tokens (r : Parser) [Parser.HasTokens r] : Parser.HasTokens (many r) :=
⟨tokens r⟩

instance many.view (r : Parser) [HasView α r] : Parser.HasView (List α) (many r) :=
/- Remark: `many1.view` can handle empty list. -/
{..many1.view r}

private def sepByAux (p : m Syntax) (sep : Parser) (allowTrailingSep : Bool) : Bool → List Syntax → Nat → Parser
| pOpt as 0     := error "unreachable"
| pOpt as (n+1) := do
  let p := if pOpt then some <$> p <|> pure none else some <$> p,
  some a ← catch p (λ msg, throw {msg with custom :=
    -- append `Syntax.missing` to make clear that List is incomplete
    Syntax.list (Syntax.missing::msg.custom.get::as).reverse})
    | pure (Syntax.list as.reverse),
  -- I don't want to think about what the output on a failed separator parse should look like
  let sep := try sep,
  some s ← some <$> sep <|> pure none
    | pure (Syntax.list (a::as).reverse),
  sepByAux allowTrailingSep (s::a::as) n

def sepBy (p sep : Parser) (allowTrailingSep := true) : Parser :=
do rem ← remaining, sepByAux p sep allowTrailingSep true [] (rem+1)

def sepBy1 (p sep : Parser) (allowTrailingSep := true) : Parser :=
do rem ← remaining, sepByAux p sep allowTrailingSep false [] (rem+1)

instance sepBy.tokens (p sep : Parser) (a) [Parser.HasTokens p] [Parser.HasTokens sep] :
  Parser.HasTokens (sepBy p sep a) :=
⟨tokens p ++ tokens sep⟩

structure SepBy.Elem.View (α β : Type) :=
(item      : α)
(separator : Option β := none)

instance SepBy.Elem.View.itemCoe {α β : Type} : HasCoeT α (SepBy.Elem.View α β) :=
⟨λ a, ⟨a, none⟩⟩

private def sepBy.viewAux {α β} (p sep : Parser) [Parser.HasView α p] [Parser.HasView β sep] :
  List Syntax → List (SepBy.Elem.View α β)
| []    := []
| [stx] := [⟨HasView.view p stx, none⟩]
| (stx1::stx2::stxs) := ⟨HasView.view p stx1, some $ HasView.view sep stx2⟩::sepBy.viewAux stxs

instance sepBy.view {α β} (p sep : Parser) (a) [Parser.HasView α p] [Parser.HasView β sep] :
  Parser.HasView (List (SepBy.Elem.View α β)) (sepBy p sep a) :=
{ view := λ stx, match stx.asNode with
    | some n := sepBy.viewAux p sep n.args
    | _ := [⟨view p Syntax.missing, none⟩],
  review := λ as, Syntax.list $ as.bind (λ a, match a with
    | ⟨v, some vsep⟩ := [review p v, review sep vsep]
    | ⟨v, none⟩      := [review p v]) }

instance sepBy1.tokens (p sep : Parser) (a) [Parser.HasTokens p] [Parser.HasTokens sep] :
  Parser.HasTokens (sepBy1 p sep a) :=
⟨tokens (sepBy p sep a)⟩

instance sepBy1.View {α β} (p sep : Parser) (a) [Parser.HasView α p] [Parser.HasView β sep] :
  Parser.HasView (List (SepBy.Elem.View α β)) (sepBy1 p sep a) :=
{..sepBy.view p sep a}

/-- Optionally parse `r`. `require` can be used to conditionally override the
    behavior without changing the structure of the syntax tree. -/
def optional (r : Parser) (require := false) : Parser :=
if require then r else
do r ← optional $
     -- on error, wrap in "some"
     catch r (λ msg, throw {msg with custom := Syntax.list [msg.custom.get]}),
   pure $ match r with
   | some r := Syntax.list [r]
   | none   := Syntax.list []

instance optional.tokens (r : Parser) [Parser.HasTokens r] (req) : Parser.HasTokens (optional r req) :=
⟨tokens r⟩
instance optional.view (r : Parser) [Parser.HasView α r] (req) : Parser.HasView (Option α) (optional r req) :=
{ view := λ stx, match stx.asNode with
    | some {args := [], ..} := none
    | some {args := [stx], ..} := some $ HasView.view r stx
    | _ := some $ view r Syntax.missing,
  review := λ a, match a with
    | some a := Syntax.list [review r a]
    | none   := Syntax.list [] }
instance optional.viewDefault (r : Parser) [Parser.HasView α r] (req) : Parser.HasViewDefault (optional r req) (Option α) none := ⟨⟩

/-- Parse a List `[p1, ..., pn]` of parsers as `p1 <|> ... <|> pn`.
    Note that there is NO explicit encoding of which Parser was chosen;
    parsers should instead produce distinct Node names for disambiguation. -/
def anyOf (rs : List Parser) : Parser :=
match rs with
| [] := error "anyOf"
| (r::rs) := rs.foldl (<|>) r

instance anyOf.tokens (rs : List Parser) [Parser.HasTokens rs] : Parser.HasTokens (anyOf rs) :=
⟨tokens rs⟩
instance anyOf.view (rs : List Parser) : Parser.HasView Syntax (anyOf rs) := default _

/-- Parse a List `[p1, ..., pn]` of parsers with `MonadParsec.longestMatch`.
    If the Result is ambiguous, wrap it in a `choice` Node.
    Note that there is NO explicit encoding of which Parser was chosen;
    parsers should instead produce distinct Node names for disambiguation. -/
def longestMatch (rs : List Parser) : Parser :=
do stxs ← MonadParsec.longestMatch rs,
   match stxs with
   | [stx] := pure stx
   | _     := pure $ Syntax.mkNode choice stxs

instance longestMatch.tokens (rs : List Parser) [Parser.HasTokens rs] : Parser.HasTokens (longestMatch rs) :=
⟨tokens rs⟩
instance longestMatch.view (rs : List Parser) : Parser.HasView Syntax (longestMatch rs) := default _

def choiceAux : List Parser → Nat → Parser
| []      _ := error "choice: Empty List"
| (r::rs) i :=
  do { stx ← r,
       pure $ Syntax.mkNode ⟨Name.mkNumeral Name.anonymous i⟩ [stx] }
  <|> choiceAux rs (i+1)

/-- Parse a List `[p1, ..., pn]` of parsers as `p1 <|> ... <|> pn`.
    The Result will be wrapped in a Node with the index of the successful
    Parser as the Name.

    Remark: Does not have a `HasView` instance because we only use it in `nodeChoice!` macros
    that define their own views. -/
def choice (rs : List Parser) : Parser :=
choiceAux rs 0

instance choice.tokens (rs : List Parser) [Parser.HasTokens rs] : Parser.HasTokens (choice rs) :=
⟨tokens rs⟩

/-- Like `choice`, but using `longestMatch`. Does not create choice nodes, prefers the first successful Parser. -/
def longestChoice (rs : List Parser) : Parser :=
do stx::stxs ← MonadParsec.longestMatch $ rs.enum.map $ λ ⟨i, r⟩, do {
     stx ← r,
     pure $ Syntax.mkNode ⟨Name.mkNumeral Name.anonymous i⟩ [stx]
   } | error "unreachable",
   pure stx

instance longestChoice.tokens (rs : List Parser) [Parser.HasTokens rs] : Parser.HasTokens (longestChoice rs) :=

⟨tokens rs⟩
instance try.tokens (r : Parser) [Parser.HasTokens r] : Parser.HasTokens (try r) :=
⟨tokens r⟩
instance try.view (r : Parser) [i : Parser.HasView α r] : Parser.HasView α (try r) :=
{..i}

instance label.tokens (r : Parser) (l) [Parser.HasTokens r] : Parser.HasTokens (label r l) :=
⟨tokens r⟩
instance label.view (r : Parser) (l) [i : Parser.HasView α r] : Parser.HasView α (label r l) :=
{..i}

instance recurse.tokens (α δ m a) [MonadRec α δ m] : Parser.HasTokens (recurse a : m δ) :=
default _ -- recursive use should not contribute any new tokens
instance recurse.view (α δ m a) [MonadRec α δ m] : Parser.HasView Syntax (recurse a : m δ) := default _

instance monadLift.tokens {m' : Type → Type} [HasMonadLiftT m m'] (r : m Syntax) [Parser.HasTokens r] :
  Parser.HasTokens (monadLift r : m' Syntax) :=
⟨tokens r⟩
instance monadLift.view {m' : Type → Type} [HasMonadLiftT m m'] (r : m Syntax) [i : Parser.HasView α r] :
  Parser.HasView α (monadLift r : m' Syntax) :=
{..i}

instance seqLeft.tokens {α : Type} (x : m α) (p : m Syntax) [Parser.HasTokens p] : Parser.HasTokens (p <* x) :=
⟨tokens p⟩
instance seqLeft.view {α β : Type} (x : m α) (p : m Syntax) [i : Parser.HasView β p] : Parser.HasView β (p <* x) :=
{..i}

instance seqRight.tokens {α : Type} (x : m α) (p : m Syntax) [Parser.HasTokens p] : Parser.HasTokens (x *> p) :=
⟨tokens p⟩
instance seqRight.view {α β : Type} (x : m α) (p : m Syntax) [i : Parser.HasView β p] : Parser.HasView β (x *> p) :=
{..i}

instance coe.tokens {β} (r : Parser) [Parser.HasTokens r] [HasCoeT Parser β]: Parser.HasTokens (coe r : β) :=
⟨tokens r⟩
instance coe.view {β} (r : Parser) [i : Parser.HasView α r] [HasCoeT Parser β] : Parser.HasView α (coe r : β) :=
{..i}
instance coe.viewDefault {β} (d : α) (r : Parser) [HasView α r] [Parser.HasViewDefault r α d] [HasCoeT Parser β] : Parser.HasViewDefault (coe r : β) α d := ⟨⟩

end Combinators
end Parser
end Lean
