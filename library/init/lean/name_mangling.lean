/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.lean.name init.lean.parser.stringliteral
namespace Lean
open Lean.Parser
open Lean.Parser.MonadParsec

private def String.mangleAux : Nat → String.Iterator → String → String
| 0     it r := r
| (i+1) it r :=
  let c := it.curr in
  if c.isAlpha || c.isDigit then
    String.mangleAux i it.next (r.push c)
  else if c = '_' then
    String.mangleAux i it.next (r ++ "__")
  else if c.toNat < 255 then
    let n := c.toNat in
    let r := r ++ "_x" in
    let r := r.push $ Nat.digitChar (n / 16) in
    let r := r.push $ Nat.digitChar (n % 16) in
    String.mangleAux i it.next r
  else
    let n := c.toNat in
    let r := r ++ "_u" in
    let r := r.push $ Nat.digitChar (n / 4096) in
    let n := n % 4096 in
    let r := r.push $ Nat.digitChar (n / 256) in
    let n := n % 256 in
    let r := r.push $ Nat.digitChar (n / 16) in
    let r := r.push $ Nat.digitChar (n % 16) in
    String.mangleAux i it.next r

def String.mangle (s : String) : String :=
String.mangleAux s.length s.mkIterator ""

private def Name.mangleAux (pre : String) : Name → String
| Name.anonymous       := pre
| (Name.mkString p s) :=
  let m := String.mangle s in
  match p with
  | Name.anonymous := m
  | _              := (Name.mangleAux p) ++ "_" ++ m
| (Name.mkNumeral p n) :=
  let r := Name.mangleAux p in
  r ++ "_" ++ toString n ++ "_"

def Name.mangle (n : Name) (pre : String := "_l") : String :=
Name.mangleAux pre n

end Lean
