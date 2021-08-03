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
  /- Invariant: non-empty and never directly nested. `append #[tag _ append #[]]` is okay. -/
  | append (as : Array (TaggedText α))
  | tag (t : α) (a : TaggedText α)
  deriving Inhabited, BEq

namespace TaggedText

partial def fromJson? [FromJson α] (j : Json) : Except String (TaggedText α) :=
  (do
    let j ← j.getObjVal? "text"
    let s ← j.getObjValAs? String "s"
    text s
  ) <|>
  (do
    let _ : FromJson (TaggedText α) := ⟨fromJson?⟩
    let j ← j.getObjVal? "append"
    let as ← j.getObjValAs? (Array (TaggedText α)) "as"
    append as
  ) <|>
  (do
    let _ : FromJson (TaggedText α) := ⟨fromJson?⟩
    let j ← j.getObjVal? "tag"
    let t ← j.getObjValAs? α "t"
    let a ← j.getObjValAs? (TaggedText α) "a"
    tag t a
  )

instance [FromJson α] : FromJson (TaggedText α) :=
  ⟨fromJson?⟩

partial def toJson [ToJson α] : TaggedText α → Json
  | text s    => Json.mkObj [("text", Json.mkObj [("s", s)])]
  | append as => Json.mkObj [("append", Json.mkObj [("as", Json.arr <| as.map toJson)])]
  | tag t a   => Json.mkObj [("tag", Json.mkObj [("t", ToJson.toJson t), ("a", toJson a)])]

instance [ToJson α] : ToJson (TaggedText α) :=
  ⟨toJson⟩

def appendText (s₀ : String) : TaggedText α → TaggedText α
  | text s    => text (s ++ s₀)
  | append as => match as.back with
    | text s => append <| as.set! (as.size - 1) <| text (s ++ s₀)
    | a      => append <| as.push (text s₀)
  | a         => append #[a, text s₀]

def appendTag (acc : TaggedText α) (t₀ : α) (a₀ : TaggedText α) : TaggedText α :=
  match acc with
  | append as => append (as.push <| tag t₀ a₀)
  | a         => append #[a, tag t₀ a₀]

partial def toString [ToString α] : TaggedText α → String
  | text s => s
  | append as => " ++ ".intercalate (as.toList.map toString)
  | tag t a => s!"([{t}] {toString a})"

partial def map (f : α → β) : TaggedText α → TaggedText β :=
  go
where go : TaggedText α → TaggedText β
  | text s => text s
  | append as => append (as.map go)
  | tag t a => tag (f t) (go a)

partial def mapM [Monad m] (f : α → m β) : TaggedText α → m (TaggedText β) :=
  go
where go : TaggedText α → m (TaggedText β)
  | text s => text s
  | append as => do append (← as.mapM go)
  | tag t a => do tag (← f t) (← go a)

partial def rewrite (f : α → TaggedText α → TaggedText β) : TaggedText α → TaggedText β :=
  go
where go : TaggedText α → TaggedText β
  | text s => text s
  | append as => append (as.map go)
  | tag t a => f t a

/-- Like `mapM` but allows rewriting the whole subtree at `tag` nodes. -/
partial def rewriteM [Monad m] (f : α → TaggedText α → m (TaggedText β)) : TaggedText α → m (TaggedText β) :=
  go
where go : TaggedText α → m (TaggedText β)
  | text s => text s
  | append as => do append (← as.mapM go)
  | tag t a => f t a

instance [RpcEncoding α β] : RpcEncoding (TaggedText α) (TaggedText β) where
  rpcEncode a := a.mapM rpcEncode
  rpcDecode a := a.mapM rpcDecode

private structure TaggedState where
  out    : TaggedText Nat := TaggedText.text ""
  column : Nat            := 0

instance : Std.Format.MonadPrettyFormat (StateM TaggedState) where
  pushOutput s       := modify fun ⟨out, col⟩ => ⟨out.appendText s, col + s.length⟩
  pushNewline indent := modify fun ⟨out, col⟩ => ⟨out.appendText ("\n".pushn ' ' indent), indent⟩
  currColumn         := return (←get).column
  withTag t x        := modifyGet fun ⟨currOut, currCol⟩ =>
    let ⟨ret, out, col⟩ := x { column := currCol }
    (ret, ⟨currOut.appendTag t out, col⟩)

def prettyTagged (f : Format) (w : Nat := Std.Format.defWidth) : TaggedText Nat :=
  (f.prettyM w : StateM TaggedState Unit) {} |>.snd.out

/-- Remove tags, leaving just the pretty-printed string. -/
partial def stripTags (tt : TaggedText α) : String :=
  go "" #[tt]
where go (acc : String) : Array (TaggedText α) → String
  | #[] => acc
  | ts  => match ts.back with
    | text s    => go (acc ++ s) ts.pop
    | append as => go acc (ts.pop ++ as)
    | tag _ a   => go acc (ts.set! (ts.size - 1) a)

end TaggedText
end Lean.Widget
