import Lean.Data.PersistentHashMap
import Lean.Data.Format
open Lean Std Lean.PersistentHashMap

abbrev Map := PersistentHashMap Nat Nat

partial def formatMap : Node Nat Nat → Format
| Node.collision keys vals _   => Format.sbracket $
  keys.size.fold
    (fun i _ fmt =>
      let k := keys[i];
      let v := vals.get! i;
      let p := if i > 0 then fmt ++ format "," ++ Format.line else fmt;
      p ++ "c@" ++ Format.paren (format k ++ " => " ++ format v))
    Format.nil
| Node.entries entries        => Format.sbracket $
  entries.size.fold
    (fun i _ fmt =>
      let entry := entries[i];
      let p := if i > 0 then fmt ++ format "," ++ Format.line else fmt;
      p ++
      match entry with
      | Entry.null      => "<null>"
      | Entry.ref node  => formatMap node
      | Entry.entry k v => Format.paren (format k ++ " => " ++ format v))
    Format.nil

def main : IO Unit :=
do
let a : Array Nat := [1, 2, 3].toArray;
IO.println (a.indexOf? 2);
let m : Map := PersistentHashMap.empty;
let m := m.insert 1 1;
let m := m.insert 33 2;
let m := m.insert 65 3;
-- IO.println (formatMap m.root);
IO.println m.stats;
let m := m.erase 33;
IO.println (m.find? 1);
IO.println (m.find? 33);
IO.println (m.find? 65);
IO.println m.stats;
let m := m.erase 1;
IO.println (m.find? 1);
IO.println (m.find? 33);
IO.println (m.find? 65);
IO.println m.stats;
let m := m.erase 1;
IO.println (m.find? 1);
IO.println (m.find? 33);
IO.println (m.find? 65);
let m := m.erase 65;
IO.println (m.find? 1);
IO.println (m.find? 33);
IO.println (m.find? 65);
IO.println m.stats
