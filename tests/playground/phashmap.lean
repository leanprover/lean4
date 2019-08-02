import init.data.persistenthashmap
import init.lean.format
open Lean PersistentHashMap

abbrev Map := PersistentHashMap Nat Nat

partial def formatMap : Node Nat Nat → Format
| (Node.collision keys vals _) := Format.sbracket $
  keys.size.fold
    (fun i fmt =>
      let k := keys.get i;
      let v := vals.get i;
      let p := if i > 0 then fmt ++ format "," ++ Format.line else fmt;
      p ++ "c@" ++ Format.paren (format k ++ " => " ++ format v))
    Format.nil
| (Node.entries entries)      := Format.sbracket $
  entries.size.fold
    (fun i fmt =>
      let entry := entries.get i;
      let p := if i > 0 then fmt ++ format "," ++ Format.line else fmt;
      p ++
      match entry with
      | Entry.null      => "<null>"
      | Entry.ref node  => formatMap node
      | Entry.entry k v => Format.paren (format k ++ " => " ++ format v))
    Format.nil

def mkMap (n : Nat) : Map :=
n.fold (fun i m => m.insert i (i*10)) PersistentHashMap.empty

def check (n : Nat) (m : Map) : IO Unit :=
n.mfor $ fun i =>
  match m.find i with
  | none   => IO.println ("failed to find " ++ toString i)
  | some v => unless (v == i*10) (IO.println ("unexpected value " ++ toString i ++ " => " ++ toString v))

def main (xs : List String) : IO Unit :=
do
let n := 1000000;
let m := mkMap n;
-- IO.println (formatMap m.root);
IO.println m.stats;
check n m
