/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Lean.Data.Json.FromToJson
import Lean.Server.Rpc.Basic

namespace Lean.Widget
open Server

/-- The minimal structure needed to represent "string with interesting (tagged) substrings".
Much like Lean 3 [`sf`](https://github.com/leanprover-community/mathlib/blob/bfa6bbbce69149792cc009ab7f9bc146181dc051/src/tactic/interactive_expr.lean#L38),
but with indentation already stringified. -/
inductive TaggedText (α : Type u) where
  | text (s : String)
  | append (a b : TaggedText α)
  | tag (t : α) (a : TaggedText α)
  deriving Inhabited, BEq, FromJson, ToJson

namespace TaggedText

-- TODO(WN): pick one depending on perf
private partial def append' : TaggedText α → TaggedText α → TaggedText α
  | text s₁,            text s₂            => text (s₁ ++ s₂)
  | text s₁,            append (text s₂) b => append' (text <| s₁ ++ s₂) b
  | append a (text s₁), text s₂            => append' a (text <| s₁ ++ s₂)
  | append a (text s₁), append (text s₂) b => append' a (append' (text <| s₁ ++ s₂) b)
  | a,                  b                  => append a b

private partial def append'' : TaggedText α → TaggedText α → TaggedText α
  | text s₁,            text s₂            => text (s₁ ++ s₂)
  | text s₁,            append (text s₂) b => append (text <| s₁ ++ s₂) b
  | append a (text s₁), text s₂            => append a (text <| s₁ ++ s₂)
  | append a (text s₁), append (text s₂) b => append a (append (text <| s₁ ++ s₂) b)
  | a,                  b                  => append a b

instance : Append (TaggedText α) where
  append := append'

def map (f : α → β) : TaggedText α → TaggedText β :=
  go
where go : TaggedText α → TaggedText β
  | text s => text s
  | append a b => append (go a) (go b)
  | tag t a => tag (f t) (go a)

def mapM [Monad m] (f : α → m β) : TaggedText α → m (TaggedText β) :=
  go
where go : TaggedText α → m (TaggedText β)
  | text s => text s
  | append a b => do append (← go a) (← go b)
  | tag t a => do tag (← f t) (← go a)

def rewrite (f : α → TaggedText α → TaggedText β) : TaggedText α → TaggedText β :=
  go
where go : TaggedText α → TaggedText β
  | text s => text s
  | append a b => append (go a) (go b)
  | tag t a => f t a

/-- Like `mapM` but allows rewriting the whole subtree at `tag` nodes. -/
def rewriteM [Monad m] (f : α → TaggedText α → m (TaggedText β)) : TaggedText α → m (TaggedText β) :=
  go
where go : TaggedText α → m (TaggedText β)
  | text s => text s
  | append a b => do append (← go a) (← go b)
  | tag t a => f t a

instance [RpcEncoding α β] : RpcEncoding (TaggedText α) (TaggedText β) where
  rpcEncode a := a.mapM rpcEncode
  rpcDecode a := a.mapM rpcDecode

private structure TaggedState where
  out    : TaggedText Nat := TaggedText.text ""
  column : Nat            := 0

instance : Std.Format.MonadPrettyFormat (StateM TaggedState) where
  pushOutput s       := modify fun ⟨out, col⟩ => ⟨out ++ text s, col + s.length⟩
  pushNewline indent := modify fun ⟨out, col⟩ => ⟨out ++ text ("\n".pushn ' ' indent), indent⟩
  currColumn         := return (←get).column
  withTag t x        := modifyGet fun ⟨currOut, currCol⟩ =>
    let ⟨ret, out, col⟩ := x { column := currCol }
    (ret, ⟨currOut ++ tag t out, col⟩)

def prettyTagged (f : Format) (w : Nat := Std.Format.defWidth) : TaggedText Nat :=
  (f.prettyM w : StateM TaggedState Unit) {} |>.snd.out

end TaggedText
end Lean.Widget
