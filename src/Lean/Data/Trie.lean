/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich, Leonardo de Moura

Trie for tokenizing the Lean language
-/
import Lean.Data.Format

namespace Lean
namespace Parser

inductive Trie (α : Type) where
  | Node : Option α → RBNode Char (fun _ => Trie α) → Trie α

namespace Trie
variable {α : Type}

def empty : Trie α :=
  ⟨none, RBNode.leaf⟩

instance : EmptyCollection (Trie α) :=
  ⟨empty⟩

instance : Inhabited (Trie α) where
  default := Node none RBNode.leaf

partial def insert (t : Trie α) (s : String) (val : α) : Trie α :=
  let rec insertEmpty (i : String.Pos) : Trie α :=
    match s.atEnd i with
    | true => Trie.Node (some val) RBNode.leaf
    | false =>
      let c := s.get i
      let t := insertEmpty (s.next i)
      Trie.Node none (RBNode.singleton c t)
  let rec loop
    | Trie.Node v m, i =>
      match s.atEnd i with
      | true  => Trie.Node (some val) m -- overrides old value
      | false =>
        let c := s.get i
        let i := s.next i
        let t := match RBNode.find compare m c with
          | none   => insertEmpty i
          | some t => loop t i
        Trie.Node v (RBNode.insert compare m c t)
  loop t 0

partial def find? (t : Trie α) (s : String) : Option α :=
  let rec loop
    | Trie.Node val m, i =>
      match s.atEnd i with
      | true  => val
      | false =>
        let c := s.get i
        let i := s.next i
        match RBNode.find compare m c with
        | none   => none
        | some t => loop t i
  loop t 0

/-- Return values that match the given `prefix` -/
partial def findPrefix (t : Trie α) (pre : String) : Array α :=
  go t 0 |>.run #[] |>.2
where
  go (t : Trie α) (i : String.Pos) : StateM (Array α) Unit :=
    if pre.atEnd i then
      collect t
    else
      let k := pre.get i
      let i := pre.next i
      let ⟨_, cs⟩ := t
      cs.forM fun k' c => do
        if k == k' then go c i

  collect (t : Trie α) : StateM (Array α) Unit := do
    let ⟨a?, cs⟩ := t
    if let some a := a? then
      modify (·.push a)
    cs.forM fun _ c => collect c

private def updtAcc (v : Option α) (i : String.Pos) (acc : String.Pos × Option α) : String.Pos × Option α :=
  match v, acc with
  | some v, (_, _) => (i, some v)  -- we pattern match on `acc` to enable memory reuse
  | none,   acc    => acc

partial def matchPrefix (s : String) (t : Trie α) (i : String.Pos) : String.Pos × Option α :=
  let rec loop
    | Trie.Node v m, i, acc =>
      match s.atEnd i with
      | true  => updtAcc v i acc
      | false =>
        let acc := updtAcc v i acc
        let c   := s.get i
        let i   := s.next i
        match RBNode.find compare m c with
        | some t => loop t i acc
        | none   => acc
  loop t i (i, none)

private partial def toStringAux {α : Type} : Trie α → List Format
  | Trie.Node _ map => map.fold (fun Fs c t =>
   format (repr c) :: (Format.group $ Format.nest 2 $ flip Format.joinSep Format.line $ toStringAux t) :: Fs) []

instance {α : Type} : ToString (Trie α) :=
  ⟨fun t => (flip Format.joinSep Format.line $ toStringAux t).pretty⟩
end Trie

end Parser
end Lean
