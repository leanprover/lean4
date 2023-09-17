/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich, Leonardo de Moura, Joachim Breitner

A string trie data strucuture, used for tokenizing the Lean language
-/
import Lean.Data.Format

namespace Lean
namespace Parser

/-
Implementation notes:
Tries have typically many nodes with small degree, where a linear scan
through the (compact) `ByteArray` is faster than using binary search or
search tress.

Moreover, many nodes have degree 1, which justifies the special case `Node1
constructors.

The code would be a bit less repetitive if we had
```
mutual
def Trie α := (Option α, ByteAssoc α)
inductive ByteAssoc α where
  | Leaf : Trie α
  | Node1 : UInt8 → Trie α → Trie α
  | Node : ByteArray -> Array (Trie α) → Trie α
end
```
but that would come at the cost of extra indirections.
-/

/-- A Trie is a key-value store where the keys are of type `String`,
and the internal structure is a tree that branches on the bytes of the string.
-/
inductive Trie (α : Type) where
  | Leaf : Option α → Trie α
  | Node1 : Option α → UInt8 → Trie α → Trie α
  | Node : Option α → ByteArray -> Array (Trie α) → Trie α

namespace Trie
variable {α : Type}

def empty : Trie α := Leaf none

instance : EmptyCollection (Trie α) :=
  ⟨empty⟩

instance : Inhabited (Trie α) where
  default := empty

partial def upsert (t : Trie α) (s : String) (f : Option α → α) : Trie α :=
  let rec insertEmpty (i : Nat) : Trie α :=
    if h : i < s.utf8ByteSize then
      let c := s.getUtf8Byte i h
      let t := insertEmpty (i + 1)
      Trie.Node1 none c t
    else
      Trie.Leaf (f .none)
  let rec loop
    | i, Leaf v =>
      if h : i < s.utf8ByteSize then
        let c := s.getUtf8Byte i h
        let t := insertEmpty (i + 1)
        Trie.Node1 v c t
      else
        Trie.Leaf (f v)
    | i, Node1 v c' t' =>
      if h : i < s.utf8ByteSize then
        let c := s.getUtf8Byte i h
        if c == c'
        then Trie.Node1 v c' (loop (i + 1) t')
        else 
          let t := insertEmpty (i + 1)
          Trie.Node v (.mk #[c, c']) #[t, t']
      else
        Trie.Node1 (f v) c' t'
    | i, Trie.Node v cs ts =>
      if h : i < s.utf8ByteSize then
        let c := s.getUtf8Byte i h
        match cs.findIdx? (· == c) with
          | none   =>
            let t := insertEmpty (i + 1)
            Trie.Node v (cs.push c) (ts.push t)
          | some idx =>
            Trie.Node v cs (ts.modify idx (loop (i + 1)))
      else
        Trie.Node (f v) cs ts
  loop 0 t

partial def insert (t : Trie α) (s : String) (val : α) : Trie α :=
  upsert t s (fun _ => val)

partial def find? (t : Trie α) (s : String) : Option α :=
  let rec loop
    | i, Trie.Leaf val =>
      if i < s.utf8ByteSize then
        none
      else
        val
    | i, Trie.Node1 val c' t' =>
      if h : i < s.utf8ByteSize then
        let c := s.getUtf8Byte i h
        if c == c'
        then loop (i + 1) t'
        else none
      else
        val
    | i, Trie.Node val cs ts =>
      if h : i < s.utf8ByteSize then
        let c := s.getUtf8Byte i h
        match cs.findIdx? (· == c) with
        | none   => none
        | some idx => loop (i + 1) (ts.get! idx)
      else
        val
  loop 0 t

/-- Return values that match the given `prefix` -/
partial def findPrefix (t : Trie α) (pre : String) : Array α :=
  go t 0 |>.run #[] |>.2
where
  go (t : Trie α) (i : Nat) : StateM (Array α) Unit :=
    if h : i < pre.utf8ByteSize then
      let c := pre.getUtf8Byte i h
      match t with
      | Leaf _val =>
        pure ()
      | Node1 _val c' t' =>
        if c == c'
        then go t' (i + 1)
        else pure ()
      | Node _val cs ts =>
        match cs.findIdx? (· == c) with
        | none   => pure ()
        | some idx => go (ts.get! idx) (i + 1)
    else
      collect t

  collect (t : Trie α) : StateM (Array α) Unit := do
    match t with
    | Leaf a? =>
      if let some a := a? then
        modify (·.push a)
    | Node1 a? _ t' =>
      if let some a := a? then
        modify (·.push a)
      collect t'
    | Node a? _ ts =>
      if let some a := a? then
        modify (·.push a)
      ts.forM fun t' => collect t'

partial def matchPrefix (s : String) (t : Trie α) (i : String.Pos) : Option α :=
  let rec loop
    | Trie.Leaf v, _, res =>
      if v.isSome then v else res
    | Trie.Node1 v c' t', i, res =>
      let res := if v.isSome then v else res
      if h : i < s.utf8ByteSize then
        let c := s.getUtf8Byte i h
        if c == c'
        then loop t' (i + 1) res
        else res
      else
        res
    | Trie.Node v cs ts, i, res =>
      let res := if v.isSome then v else res
      if h : i < s.utf8ByteSize then
        let c := s.getUtf8Byte i h
        match cs.findIdx? (· == c) with
        | none => res
        | some idx => loop (ts.get! idx) (i + 1) res
      else
        res
  loop t i.byteIdx none

private partial def toStringAux {α : Type} : Trie α → List Format
  | Trie.Leaf _ => []
  | Trie.Node1 _ c t =>
    [ format (repr c), Format.group $ Format.nest 4 $ flip Format.joinSep Format.line $ toStringAux t ]
  | Trie.Node _ cs ts =>
    List.join $ List.zipWith (fun c t =>
      [ format (repr c), (Format.group $ Format.nest 4 $ flip Format.joinSep Format.line $ toStringAux t) ]
    ) cs.toList ts.toList

instance {α : Type} : ToString (Trie α) :=
  ⟨fun t => (flip Format.joinSep Format.line $ toStringAux t).pretty⟩

end Trie

end Parser
end Lean