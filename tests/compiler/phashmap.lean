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

def mkMap (n : Nat) : Map :=
n.fold (fun i _ m => m.insert i (i*10)) PersistentHashMap.empty

def check (n : Nat) (m : Map) : IO Unit :=
n.forM $ fun i _ => do
  match m.find? i with
  | none   => IO.println s!"failed to find {i}"
  | some v => unless v == i*10 do IO.println s!"unexpected value {i} => {v}"

def delOdd (n : Nat) (m : Map) : Map :=
n.fold (fun i _ m => if i % 2 == 0 then m else m.erase i) m

def check2 (n : Nat) (bot : Nat) (m : Map) : IO Unit :=
n.forM $ fun i _ => do
  if i % 2 == 0 && i >= bot then
    match m.find? i with
    | none   => IO.println s!"failed to find {i}"
    | some v => unless v == i*10 do IO.println s!"unexpected value {i} => {v}"
  else
    unless m.find? i == none do IO.println s!"mapping still contains {i}"

def delLess (n : Nat) (m : Map) : Map :=
n.fold (fun i _ m => m.erase i) m

def main (xs : List String) : IO Unit :=
do
let n := 5000;
let m := mkMap n;
-- IO.println (formatMap m.root);
IO.println m.stats;
check n m;
let m := delOdd n m;
IO.println m.stats;
check2 n 0 m;
let m := delLess 4900 m;
check2 n 4900 m;
IO.println m.stats;
let m := delLess 4990 m;
check2 n 4990 m;
IO.println m.stats
