import init.data.persistenthashmap
import init.lean.format
open Lean PersistentHashMap

abbrev Map := PersistentHashMap Nat Nat

partial def formatMap : Node Nat Nat → Format
| Node.collision keys vals _   => Format.sbracket $
  keys.size.fold
    (fun i fmt =>
      let k := keys.get i;
      let v := vals.get i;
      let p := if i > 0 then fmt ++ format "," ++ Format.line else fmt;
      p ++ "c@" ++ Format.paren (format k ++ " => " ++ format v))
    Format.nil
| Node.entries entries        => Format.sbracket $
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

def delOdd (n : Nat) (m : Map) : Map :=
n.fold (fun i m => if i % 2 == 0 then m else m.erase i) m

def check2 (n : Nat) (bot : Nat) (m : Map) : IO Unit :=
n.mfor $ fun i =>
  if i % 2 == 0 && i >= bot then
    match m.find i with
    | none   => IO.println ("failed to find " ++ toString i)
    | some v => unless (v == i*10) (IO.println ("unexpected value " ++ toString i ++ " => " ++ toString v))
  else
    unless (m.find i == none) (IO.println ("mapping still contains " ++ toString i))

def delLess (n : Nat) (m : Map) : Map :=
n.fold (fun i m => m.erase i) m

def checkContains (n : Nat) (m : Map) : IO Unit :=
n.mfor $ fun i =>
  match m.find i with
  | none   => unless (!m.contains i) (IO.println "bug at contains!")
  | some _ => unless (m.contains i) (IO.println "bug at contains!")

def main (xs : List String) : IO Unit :=
do
let n := 500000;
let m := mkMap n;
-- IO.println (formatMap m.root);
IO.println m.stats;
check n m;
checkContains n m;
let m := delOdd n m;
IO.println m.stats;
check2 n 0 m;
checkContains n m;
let m := delLess 499000 m;
check2 n 499000 m;
IO.println m.size;
IO.println m.stats;
let m := delLess 499900 m;
check2 n 499900 m;
checkContains n m;
IO.println m.size;
IO.println m.stats
