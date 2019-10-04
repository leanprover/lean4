/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich, Leonardo de Moura

Trie for tokenizing the Lean language
-/
prelude
import Init.Data.Rbmap
import Init.Lean.Format

namespace Lean
namespace Parser

inductive Trie (α : Type)
| Node : Option α → RBNode Char (fun _ => Trie) → Trie

namespace Trie
variables {α : Type}

def empty : Trie α :=
⟨none, RBNode.leaf⟩

instance : HasEmptyc (Trie α) :=
⟨empty⟩

instance : Inhabited (Trie α) :=
⟨Node none RBNode.leaf⟩

private partial def insertEmptyAux (s : String) (val : α) : String.Pos → Trie α
| i => match s.atEnd i with
  | true => Trie.Node (some val) RBNode.leaf
  | false =>
    let c := s.get i;
    let t := insertEmptyAux (s.next i);
    Trie.Node none (RBNode.singleton c t)

private partial def insertAux (s : String) (val : α) : Trie α → String.Pos → Trie α
| Trie.Node v m, i =>
  match s.atEnd i with
  | true  => Trie.Node (some val) m -- overrides old value
  | false =>
    let c := s.get i;
    let i := s.next i;
    let t := match RBNode.find Char.lt m c with
      | none   => insertEmptyAux s val i
      | some t => insertAux t i;
    Trie.Node v (RBNode.insert Char.lt m c t)

def insert (t : Trie α) (s : String) (val : α) : Trie α :=
insertAux s val t 0

private partial def findAux (s : String) : Trie α → String.Pos → Option α
| Trie.Node val m, i =>
  match s.atEnd i with
  | true  => val
  | false =>
    let c := s.get i;
    let i := s.next i;
    match RBNode.find Char.lt m c with
    | none   => none
    | some t => findAux t i

def find (t : Trie α) (s : String) : Option α :=
findAux s t 0

private def updtAcc (v : Option α) (i : String.Pos) (acc : String.Pos × Option α) : String.Pos × Option α :=
match v, acc with
| some v, (j, w) => (i, some v)  -- we pattern match on `acc` to enable memory reuse
| none,   acc    => acc

private partial def matchPrefixAux (s : String) : Trie α → String.Pos → (String.Pos × Option α) → String.Pos × Option α
| Trie.Node v m, i, acc =>
  match s.atEnd i with
  | true  => updtAcc v i acc
  | false =>
    let acc := updtAcc v i acc;
    let c   := s.get i;
    let i   := s.next i;
    match RBNode.find Char.lt m c with
    | some t => matchPrefixAux t i acc
    | none   => acc

def matchPrefix (s : String) (t : Trie α) (i : String.Pos) : String.Pos × Option α :=
matchPrefixAux s t i (i, none)

private partial def toStringAux {α : Type} : Trie α → List Format
| Trie.Node val map => map.fold (fun Fs c t =>
  format (repr c) :: (Format.group $ Format.nest 2 $ flip Format.joinSep Format.line $ toStringAux t) :: Fs) []

instance {α : Type} : HasToString (Trie α) :=
⟨fun t => (flip Format.joinSep Format.line $ toStringAux t).pretty⟩
end Trie

end Parser
end Lean
