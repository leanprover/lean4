/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.lean.name
namespace Lean

private def String.mangleAux : Nat → String.Iterator → String → String
| 0,   it, r => r
| i+1, it, r =>
  let c := it.curr;
  if c.isAlpha || c.isDigit then
    String.mangleAux i it.next (r.push c)
  else if c = '_' then
    String.mangleAux i it.next (r ++ "__")
  else if c.toNat < 255 then
    let n := c.toNat;
    let r := r ++ "_x";
    let r := r.push $ Nat.digitChar (n / 16);
    let r := r.push $ Nat.digitChar (n % 16);
    String.mangleAux i it.next r
  else
    let n := c.toNat;
    let r := r ++ "_u";
    let r := r.push $ Nat.digitChar (n / 4096);
    let n := n % 4096;
    let r := r.push $ Nat.digitChar (n / 256);
    let n := n % 256;
    let r := r.push $ Nat.digitChar (n / 16);
    let r := r.push $ Nat.digitChar (n % 16);
    String.mangleAux i it.next r

def String.mangle (s : String) : String :=
String.mangleAux s.length s.mkIterator ""

private def Name.mangleAux : Name → String
| Name.anonymous    => ""
| Name.mkString p s =>
  let m := String.mangle s;
  match p with
  | Name.anonymous => m
  | _              => Name.mangleAux p ++ "_" ++ m
| Name.mkNumeral p n => Name.mangleAux p ++ "_" ++ toString n ++ "_"

@[export lean_name_mangle]
def Name.mangle (n : Name) (pre : String := "l_") : String :=
pre ++ Name.mangleAux n

end Lean
