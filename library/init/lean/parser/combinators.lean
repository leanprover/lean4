/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Syntax-tree creating Parser Combinators
-/
prelude
import init.Lean.Parser.basic
import init.data.List.instances

namespace Lean
namespace Parser

namespace Combinators
open HasTokens HasView MonadParsec

variables {α : Type} {m : Type → Type}
local notation `Parser` := m Syntax
variables [Monad m] [MonadExcept (Parsec.Message Syntax) m] [MonadParsec Syntax m] [Alternative m]

def Node (k : SyntaxNodeKind) (rs : List Parser) : Parser :=
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

@[reducible] def Seq : List Parser → Parser := Node noKind

instance Node.tokens (k) (rs : List Parser) [Parser.HasTokens rs] : Parser.HasTokens (Node k rs) :=
⟨tokens rs⟩

instance Node.View (k) (rs : List Parser) [i : HasView α k] : Parser.HasView α (Node k rs) :=
{ View := i.View, review := i.review }

-- Each Parser Combinator comes equipped with `HasView` and `HasTokens` instances

private def many1Aux (p : Parser) : List Syntax → Nat → Parser
| as 0     := error "unreachable"
| as (n+1) := do
  a ← catch p (λ msg, throw {msg with custom :=
    -- append `Syntax.missing` to make clear that List is incomplete
    Syntax.List (Syntax.missing::msg.custom.get::as).reverse}),
  many1Aux (a::as) n <|> pure (Syntax.List (a::as).reverse)

def many1 (r : Parser) : Parser :=
do rem ← remaining, many1Aux r [] (rem+1)

instance many1.tokens (r : Parser) [Parser.HasTokens r] : Parser.HasTokens (many1 r) :=
⟨tokens r⟩

instance many1.View (r : Parser) [Parser.HasView α r] : Parser.HasView (List α) (many1 r) :=
{ View := λ stx, match stx.asNode with
    | some n := n.args.map (HasView.View r)
    | _ := [HasView.View r Syntax.missing],
  review := λ as, Syntax.List $ as.map (review r) }

def many (r : Parser) : Parser :=
many1 r <|> pure (Syntax.List [])

instance many.tokens (r : Parser) [Parser.HasTokens r] : Parser.HasTokens (many r) :=
⟨tokens r⟩

instance many.View (r : Parser) [HasView α r] : Parser.HasView (List α) (many r) :=
/- Remark: `many1.View` can handle Empty List. -/
{..many1.View r}

private def sepByAux (p : m Syntax) (sep : Parser) (allowTrailingSep : Bool) : Bool → List Syntax → Nat → Parser
| pOpt as 0     := error "unreachable"
| pOpt as (n+1) := do
  let p := if pOpt then some <$> p <|> pure none else some <$> p,
  some a ← catch p (λ msg, throw {msg with custom :=
    -- append `Syntax.missing` to make clear that List is incomplete
    Syntax.List (Syntax.missing::msg.custom.get::as).reverse})
    | pure (Syntax.List as.reverse),
  -- I don't want to think about what the output on a failed separator parse should look like
  let sep := try sep,
  some s ← some <$> sep <|> pure none
    | pure (Syntax.List (a::as).reverse),
  sepByAux allowTrailingSep (s::a::as) n

def SepBy (p sep : Parser) (allowTrailingSep := tt) : Parser :=
do rem ← remaining, sepByAux p sep allowTrailingSep tt [] (rem+1)

def sepBy1 (p sep : Parser) (allowTrailingSep := tt) : Parser :=
do rem ← remaining, sepByAux p sep allowTrailingSep ff [] (rem+1)

instance SepBy.tokens (p sep : Parser) (a) [Parser.HasTokens p] [Parser.HasTokens sep] :
  Parser.HasTokens (SepBy p sep a) :=
⟨tokens p ++ tokens sep⟩

structure SepBy.Elem.View (α β : Type) :=
(item      : α)
(separator : Option β := none)

instance SepBy.Elem.View.itemCoe {α β : Type} : HasCoeT α (SepBy.Elem.View α β) :=
⟨λ a, ⟨a, none⟩⟩

private def SepBy.viewAux {α β} (p sep : Parser) [Parser.HasView α p] [Parser.HasView β sep] :
  List Syntax → List (SepBy.Elem.View α β)
| []    := []
| [stx] := [⟨HasView.View p stx, none⟩]
| (stx1::stx2::stxs) := ⟨HasView.View p stx1, some $ HasView.View sep stx2⟩::SepBy.viewAux stxs

instance SepBy.View {α β} (p sep : Parser) (a) [Parser.HasView α p] [Parser.HasView β sep] :
  Parser.HasView (List (SepBy.Elem.View α β)) (SepBy p sep a) :=
{ View := λ stx, match stx.asNode with
    | some n := SepBy.viewAux p sep n.args
    | _ := [⟨View p Syntax.missing, none⟩],
  review := λ as, Syntax.List $ as.bind (λ a, match a with
    | ⟨v, some vsep⟩ := [review p v, review sep vsep]
    | ⟨v, none⟩      := [review p v]) }

instance sepBy1.tokens (p sep : Parser) (a) [Parser.HasTokens p] [Parser.HasTokens sep] :
  Parser.HasTokens (sepBy1 p sep a) :=
⟨tokens (SepBy p sep a)⟩

instance sepBy1.View {α β} (p sep : Parser) (a) [Parser.HasView α p] [Parser.HasView β sep] :
  Parser.HasView (List (SepBy.Elem.View α β)) (sepBy1 p sep a) :=
{..SepBy.View p sep a}

def optional (r : Parser) : Parser :=
do r ← optional $
     -- on error, wrap in "some"
     catch r (λ msg, throw {msg with custom := Syntax.List [msg.custom.get]}),
   pure $ match r with
   | some r := Syntax.List [r]
   | none   := Syntax.List []

instance optional.tokens (r : Parser) [Parser.HasTokens r] : Parser.HasTokens (optional r) :=
⟨tokens r⟩
instance optional.View (r : Parser) [Parser.HasView α r] : Parser.HasView (Option α) (optional r) :=
{ View := λ stx, match stx.asNode with
    | some {args := [], ..} := none
    | some {args := [stx], ..} := some $ HasView.View r stx
    | _ := some $ View r Syntax.missing,
  review := λ a, match a with
    | some a := Syntax.List [review r a]
    | none   := Syntax.List [] }
instance optional.viewDefault (r : Parser) [Parser.HasView α r] : Parser.HasViewDefault (optional r) (Option α) none := ⟨⟩

/-- Parse a List `[p1, ..., pn]` of parsers as `p1 <|> ... <|> pn`.
    Note that there is NO explicit encoding of which Parser was chosen;
    parsers should instead produce distinct Node names for disambiguation. -/
def anyOf (rs : List Parser) : Parser :=
match rs with
| [] := error "anyOf"
| (r::rs) := rs.foldl (<|>) r

instance anyOf.tokens (rs : List Parser) [Parser.HasTokens rs] : Parser.HasTokens (anyOf rs) :=
⟨tokens rs⟩
instance anyOf.View (rs : List Parser) : Parser.HasView Syntax (anyOf rs) := default _

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
instance longestMatch.View (rs : List Parser) : Parser.HasView Syntax (longestMatch rs) := default _

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
instance try.View (r : Parser) [i : Parser.HasView α r] : Parser.HasView α (try r) :=
{..i}

instance label.tokens (r : Parser) (l) [Parser.HasTokens r] : Parser.HasTokens (label r l) :=
⟨tokens r⟩
instance label.View (r : Parser) (l) [i : Parser.HasView α r] : Parser.HasView α (label r l) :=
{..i}

instance recurse.tokens (α δ m a) [MonadRec α δ m] : Parser.HasTokens (recurse a : m δ) :=
default _ -- recursive use should not contribute any new tokens
instance recurse.View (α δ m a) [MonadRec α δ m] : Parser.HasView Syntax (recurse a : m δ) := default _

instance monadLift.tokens {m' : Type → Type} [HasMonadLiftT m m'] (r : m Syntax) [Parser.HasTokens r] :
  Parser.HasTokens (monadLift r : m' Syntax) :=
⟨tokens r⟩
instance monadLift.View {m' : Type → Type} [HasMonadLiftT m m'] (r : m Syntax) [i : Parser.HasView α r] :
  Parser.HasView α (monadLift r : m' Syntax) :=
{..i}

instance seqLeft.tokens {α : Type} (x : m α) (p : m Syntax) [Parser.HasTokens p] : Parser.HasTokens (p <* x) :=
⟨tokens p⟩
instance seqLeft.View {α β : Type} (x : m α) (p : m Syntax) [i : Parser.HasView β p] : Parser.HasView β (p <* x) :=
{..i}

instance seqRight.tokens {α : Type} (x : m α) (p : m Syntax) [Parser.HasTokens p] : Parser.HasTokens (x *> p) :=
⟨tokens p⟩
instance seqRight.View {α β : Type} (x : m α) (p : m Syntax) [i : Parser.HasView β p] : Parser.HasView β (x *> p) :=
{..i}

instance coe.tokens {β} (r : Parser) [Parser.HasTokens r] [HasCoeT Parser β]: Parser.HasTokens (coe r : β) :=
⟨tokens r⟩
instance coe.View {β} (r : Parser) [i : Parser.HasView α r] [HasCoeT Parser β] : Parser.HasView α (coe r : β) :=
{..i}
instance coe.viewDefault {β} (d : α) (r : Parser) [HasView α r] [Parser.HasViewDefault r α d] [HasCoeT Parser β] : Parser.HasViewDefault (coe r : β) α d := ⟨⟩

end Combinators
end Parser
end Lean
