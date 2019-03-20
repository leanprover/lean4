/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.lean.name init.lean.parser.stringLiteral
namespace lean
open lean.parser
open lean.parser.monadParsec

private def string.mangleAux : nat → string.iterator → string → string
| 0     it r := r
| (i+1) it r :=
  let c := it.curr in
  if c.isAlpha || c.isDigit then
    string.mangleAux i it.next (r.push c)
  else if c = '_' then
    string.mangleAux i it.next (r ++ "__")
  else if c.toNat < 255 then
    let n := c.toNat in
    let r := r ++ "_x" in
    let r := r.push $ nat.digitChar (n / 16) in
    let r := r.push $ nat.digitChar (n % 16) in
    string.mangleAux i it.next r
  else
    let n := c.toNat in
    let r := r ++ "_u" in
    let r := r.push $ nat.digitChar (n / 4096) in
    let n := n % 4096 in
    let r := r.push $ nat.digitChar (n / 256) in
    let n := n % 256 in
    let r := r.push $ nat.digitChar (n / 16) in
    let r := r.push $ nat.digitChar (n % 16) in
    string.mangleAux i it.next r

def string.mangle (s : string) : string :=
string.mangleAux s.length s.mkIterator ""

private def parseMangledStringAux : nat → string → parsec' string
| 0     r := pure r
| (i+1) r :=
     (eoi *> pure r)
 <|> (do c ← alpha, parseMangledStringAux i (r.push c))
 <|> (do c ← digit, parseMangledStringAux i (r.push c))
 <|> (do str "__", parseMangledStringAux i (r.push '_'))
 <|> (do str "_x", d₂ ← parseHexDigit, d₁ ← parseHexDigit,
         parseMangledStringAux i (r.push (char.ofNat (d₂ * 16 + d₁))))
 <|> (do str "_u", d₄ ← parseHexDigit, d₃ ← parseHexDigit, d₂ ← parseHexDigit, d₁ ← parseHexDigit,
         parseMangledStringAux i (r.push (char.ofNat (d₄ * 4096 + d₃ * 256 + d₂ * 16 + d₁))))

private def parseMangledString : parsec' string :=
do r ← remaining, parseMangledStringAux r ""

def string.demangle (s : string) : option string :=
(parsec.parse parseMangledString s).toOption

private def name.mangleAux (pre : string) : name → string
| name.anonymous       := pre
| (name.mkString p s) :=
  let r := name.mangleAux p in
  let m := string.mangle s in
  r ++ "_s" ++ toString m.length ++ "_" ++ m
| (name.mkNumeral p n) :=
  let r := name.mangleAux p in
  r ++ "_" ++ toString n ++ "_"

def name.mangle (n : name) (pre : string := "_l") : string :=
name.mangleAux pre n

private def parseMangledNameAux : nat → name → parsec' name
| 0 r     := pure r
| (i+1) r :=
      (eoi *> pure r)
  <|> (do str "_s", n ← num, ch '_',
          (some s) ← string.demangle <$> take n,
          parseMangledNameAux i (r.mkString s))
  <|> (do ch '_', n ← num, ch '_',
          parseMangledNameAux i (r.mkNumeral n))

private def parseMangledName (pre : string) : parsec' name :=
do str pre, r ← remaining, parseMangledNameAux r name.anonymous

def name.demangle (s : string) (pre : string := "_l") : option name :=
(parsec.parse (parseMangledName pre) s).toOption

end lean
