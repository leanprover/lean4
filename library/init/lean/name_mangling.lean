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

private def parseMangledStringAux : Nat → String → Parsec' String
| 0     r := pure r
| (i+1) r :=
     (eoi *> pure r)
 <|> (do c ← alpha, parseMangledStringAux i (r.push c))
 <|> (do c ← digit, parseMangledStringAux i (r.push c))
 <|> (do str "__", parseMangledStringAux i (r.push '_'))
 <|> (do str "_x", d₂ ← parseHexDigit, d₁ ← parseHexDigit,
         parseMangledStringAux i (r.push (Char.ofNat (d₂ * 16 + d₁))))
 <|> (do str "_u", d₄ ← parseHexDigit, d₃ ← parseHexDigit, d₂ ← parseHexDigit, d₁ ← parseHexDigit,
         parseMangledStringAux i (r.push (Char.ofNat (d₄ * 4096 + d₃ * 256 + d₂ * 16 + d₁))))

private def parseMangledString : Parsec' String :=
do r ← remaining, parseMangledStringAux r ""

def String.demangle (s : String) : Option String :=
(Parsec.parse parseMangledString s).toOption

private def Name.mangleAux (pre : String) : Name → String
| Name.anonymous       := pre
| (Name.mkString p s) :=
  let r := Name.mangleAux p in
  let m := String.mangle s in
  r ++ "_s" ++ toString m.length ++ "_" ++ m
| (Name.mkNumeral p n) :=
  let r := Name.mangleAux p in
  r ++ "_" ++ toString n ++ "_"

def Name.mangle (n : Name) (pre : String := "_l") : String :=
Name.mangleAux pre n

private def parseMangledNameAux : Nat → Name → Parsec' Name
| 0 r     := pure r
| (i+1) r :=
      (eoi *> pure r)
  <|> (do str "_s", n ← num, ch '_',
          (some s) ← String.demangle <$> take n,
          parseMangledNameAux i (r.mkString s))
  <|> (do ch '_', n ← num, ch '_',
          parseMangledNameAux i (r.mkNumeral n))

private def parseMangledName (pre : String) : Parsec' Name :=
do str pre, r ← remaining, parseMangledNameAux r Name.anonymous

def Name.demangle (s : String) (pre : String := "_l") : Option Name :=
(Parsec.parse (parseMangledName pre) s).toOption

end Lean
