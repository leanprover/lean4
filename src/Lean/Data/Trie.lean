/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich, Leonardo de Moura, Joachim Breitner

A string trie data structure, used for tokenizing the Lean language
-/
prelude
import Lean.Data.Format

namespace Lean
namespace Data

/-
## Implementation notes

Tries have typically many nodes with small degree, where a linear scan
through the (compact) `ByteArray` is faster than using binary search or
search trees like `RBTree`.

Moreover, many nodes have degree 1, which justifies the special case `Node1`
constructor.

The code would be a bit less repetitive if we used something like the following
```
mutual
def Trie α := Option α × ByteAssoc α

inductive ByteAssoc α where
  | leaf : Trie α
  | node1 : UInt8 → Trie α → Trie α
  | node : ByteArray → Array (Trie α) → Trie α
end
```
but that would come at the cost of extra indirections.
-/

/-- A Trie is a key-value store where the keys are of type `String`,
and the internal structure is a tree that branches on the bytes of the string.  -/
inductive Trie (α : Type) where
  | leaf : Option α → Trie α
  | node1 : Option α → UInt8 → Trie α → Trie α
  | node : Option α → ByteArray → Array (Trie α) → Trie α

namespace Trie
variable {α : Type}

/-- The empty `Trie` -/
def empty : Trie α := leaf none

instance : EmptyCollection (Trie α) :=
  ⟨empty⟩

instance : Inhabited (Trie α) where
  default := empty

/-- Insert or update the value at a the given key `s`.  -/
partial def upsert (t : Trie α) (s : String) (f : Option α → α) : Trie α :=
  let rec insertEmpty (i : Nat) : Trie α :=
    if h : i < s.utf8ByteSize then
      let c := s.getUtf8Byte i h
      let t := insertEmpty (i + 1)
      node1 none c t
    else
      leaf (f .none)
  let rec loop
    | i, leaf v =>
      if h : i < s.utf8ByteSize then
        let c := s.getUtf8Byte i h
        let t := insertEmpty (i + 1)
        node1 v c t
      else
        leaf (f v)
    | i, node1 v c' t' =>
      if h : i < s.utf8ByteSize then
        let c := s.getUtf8Byte i h
        if c == c'
        then node1 v c' (loop (i + 1) t')
        else
          let t := insertEmpty (i + 1)
          node v (.mk #[c, c']) #[t, t']
      else
        node1 (f v) c' t'
    | i, node v cs ts =>
      if h : i < s.utf8ByteSize then
        let c := s.getUtf8Byte i h
        match cs.findIdx? (· == c) with
          | none   =>
            let t := insertEmpty (i + 1)
            node v (cs.push c) (ts.push t)
          | some idx =>
            node v cs (ts.modify idx (loop (i + 1)))
      else
        node (f v) cs ts
  loop 0 t

/-- Inserts a value at a the given key `s`, overriding an existing value if present. -/
partial def insert (t : Trie α) (s : String) (val : α) : Trie α :=
  upsert t s (fun _ => val)

/-- Looks up a value at the given key `s`.  -/
partial def find? (t : Trie α) (s : String) : Option α :=
  let rec loop
    | i, leaf val =>
      if i < s.utf8ByteSize then
        none
      else
        val
    | i, node1 val c' t' =>
      if h : i < s.utf8ByteSize then
        let c := s.getUtf8Byte i h
        if c == c'
        then loop (i + 1) t'
        else none
      else
        val
    | i, node val cs ts =>
      if h : i < s.utf8ByteSize then
        let c := s.getUtf8Byte i h
        match cs.findIdx? (· == c) with
        | none   => none
        | some idx => loop (i + 1) ts[idx]!
      else
        val
  loop 0 t

/-- Returns an `Array` of all values in the trie, in no particular order. -/
partial def values (t : Trie α) : Array α := go t |>.run #[] |>.2
  where
    go : Trie α → StateM (Array α) Unit
      | leaf a? => do
        if let some a := a? then
          modify (·.push a)
      | node1 a? _ t' => do
        if let some a := a? then
          modify (·.push a)
        go t'
      | node a? _ ts => do
        if let some a := a? then
          modify (·.push a)
        ts.forM fun t' => go t'

/-- Returns all values whose key have the given string `pre` as a prefix, in no particular order. -/
partial def findPrefix (t : Trie α) (pre : String) : Array α := go t 0
  where
    go (t : Trie α) (i : Nat) : Array α :=
      if h : i < pre.utf8ByteSize then
        let c := pre.getUtf8Byte i h
        match t with
        | leaf _val => .empty
        | node1 _val c' t' =>
          if c == c'
          then go t' (i + 1)
          else .empty
        | node _val cs ts =>
          match cs.findIdx? (· == c) with
          | none   => .empty
          | some idx => go ts[idx]! (i + 1)
      else
        t.values

/-- Find the longest _key_ in the trie that is contained in the given string `s` at position `i`,
and return the associated value. -/
partial def matchPrefix (s : String) (t : Trie α) (i : String.Pos) : Option α :=
  let rec loop
    | leaf v, _, res =>
      if v.isSome then v else res
    | node1 v c' t', i, res =>
      let res := if v.isSome then v else res
      if h : i < s.utf8ByteSize then
        let c := s.getUtf8Byte i h
        if c == c'
        then loop t' (i + 1) res
        else res
      else
        res
    | node v cs ts, i, res =>
      let res := if v.isSome then v else res
      if h : i < s.utf8ByteSize then
        let c := s.getUtf8Byte i h
        match cs.findIdx? (· == c) with
        | none => res
        | some idx => loop ts[idx]! (i + 1) res
      else
        res
  loop t i.byteIdx none

private partial def toStringAux {α : Type} : Trie α → List Format
  | leaf _ => []
  | node1 _ c t =>
    [ format (repr c), Format.group $ Format.nest 4 $ flip Format.joinSep Format.line $ toStringAux t ]
  | node _ cs ts =>
    List.flatten $ List.zipWith (fun c t =>
      [ format (repr c), (Format.group $ Format.nest 4 $ flip Format.joinSep Format.line $ toStringAux t) ]
    ) cs.toList ts.toList

instance {α : Type} : ToString (Trie α) :=
  ⟨fun t => (flip Format.joinSep Format.line $ toStringAux t).pretty⟩

end Trie

end Data
end Lean
