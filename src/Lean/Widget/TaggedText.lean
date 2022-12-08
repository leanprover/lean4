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
  | text   : String → TaggedText α
  /-- Invariants:
  - non-empty
  - no adjacent `text` elements (they should be collapsed)
  - no directly nested `append`s (but `append #[tag _ (append ..)]` is okay) -/
  | append : Array (TaggedText α) → TaggedText α
  | tag    : α → TaggedText α → TaggedText α
  deriving Inhabited, BEq, Repr, FromJson, ToJson

namespace TaggedText

def appendText (s₀ : String) : TaggedText α → TaggedText α
  | text s    => text (s ++ s₀)
  | append as => match as.back with
    | text s => append <| as.set! (as.size - 1) <| text (s ++ s₀)
    | _      => append <| as.push (text s₀)
  | a         => append #[a, text s₀]

def appendTag (acc : TaggedText α) (t₀ : α) (a₀ : TaggedText α) : TaggedText α :=
  match acc with
  | append as => append (as.push <| tag t₀ a₀)
  | text ""   => tag t₀ a₀
  | a         => append #[a, tag t₀ a₀]

variable (f : α → β) in
partial def map : TaggedText α → TaggedText β
  | text s => text s
  | append as => append (as.map map)
  | tag t a => tag (f t) (map a)

variable [Monad m] (f : α → m β) in
partial def mapM : TaggedText α → m (TaggedText β)
  | text s => return text s
  | append as => return append (← as.mapM mapM)
  | tag t a => return tag (← f t) (← mapM a)

variable (f : α → TaggedText α → TaggedText β) in
partial def rewrite : TaggedText α → TaggedText β
  | text s => text s
  | append as => append (as.map rewrite)
  | tag t a => f t a

variable [Monad m] (f : α → TaggedText α → m (TaggedText β)) in
/-- Like `mapM` but allows rewriting the whole subtree at `tag` nodes. -/
partial def rewriteM : TaggedText α → m (TaggedText β)
  | text s => return text s
  | append as => return append (← as.mapM rewriteM)
  | tag t a => f t a

instance [RpcEncodable α] : RpcEncodable (TaggedText α) where
  rpcEncode a := toJson <$> a.mapM rpcEncode
  rpcDecode a := do TaggedText.mapM rpcDecode (← fromJson? a)

private structure TaggedState where
  out      : TaggedText (Nat × Nat)              := TaggedText.text ""
  tagStack : List (Nat × Nat × TaggedText (Nat × Nat)) := []
  column   : Nat                                 := 0
  deriving Inhabited

instance : Std.Format.MonadPrettyFormat (StateM TaggedState) where
  pushOutput s       := modify fun ⟨out, ts, col⟩ => ⟨out.appendText s, ts, col + s.length⟩
  pushNewline indent := modify fun ⟨out, ts, _⟩ => ⟨out.appendText ("\n".pushn ' ' indent), ts, indent⟩
  currColumn         := return (←get).column
  startTag n         := modify fun ⟨out, ts, col⟩ => ⟨TaggedText.text "", (n, col, out) :: ts, col⟩
  endTags n          := modify fun ⟨out, ts, col⟩ =>
    let (ended, left) := (ts.take n, ts.drop n)
    let out' := ended.foldl (init := out) fun acc (n, col', top) => top.appendTag (n, col') acc
    ⟨out', left, col⟩

/-- The output is tagged with `(tag, indent)` where `tag` is from the input `Format` and `indent`
is the indentation level at this point. The latter is used to print sub-trees accurately by passing
it again as the `indent` argument. -/
def prettyTagged (f : Format) (indent := 0) (w : Nat := Std.Format.defWidth) : TaggedText (Nat × Nat) :=
  (f.prettyM w indent : StateM TaggedState Unit) {} |>.snd.out

/-- Remove tags, leaving just the pretty-printed string. -/
partial def stripTags (tt : TaggedText α) : String :=
  go "" #[tt]
where go (acc : String) : Array (TaggedText α) → String
  | #[] => acc
  | ts  => match ts.back with
    | text s    => go (acc ++ s) ts.pop
    | append as => go acc (ts.pop ++ as.reverse)
    | tag _ a   => go acc (ts.set! (ts.size - 1) a)

end TaggedText
end Lean.Widget
