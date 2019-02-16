/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.lean.name init.lean.parser.string_literal
namespace lean
open lean.parser
open lean.parser.monad_parsec

private def string.mangle_aux : nat → string.iterator → string → string
| 0     it r := r
| (i+1) it r :=
  let c := it.curr in
  if c.is_alpha || c.is_digit then
    string.mangle_aux i it.next (r.push c)
  else if c = '_' then
    string.mangle_aux i it.next (r ++ "__")
  else if c.to_nat < 255 then
    let n := c.to_nat in
    let r := r ++ "_x" in
    let r := r.push $ nat.digit_char (n / 16) in
    let r := r.push $ nat.digit_char (n % 16) in
    string.mangle_aux i it.next r
  else
    let n := c.to_nat in
    let r := r ++ "_u" in
    let r := r.push $ nat.digit_char (n / 4096) in
    let n := n % 4096 in
    let r := r.push $ nat.digit_char (n / 256) in
    let n := n % 256 in
    let r := r.push $ nat.digit_char (n / 16) in
    let r := r.push $ nat.digit_char (n % 16) in
    string.mangle_aux i it.next r

def string.mangle (s : string) : string :=
string.mangle_aux s.length s.mk_iterator ""

private def parse_mangled_string_aux : nat → string → parsec' string
| 0     r := pure r
| (i+1) r :=
     (eoi *> pure r)
 <|> (do c ← alpha, parse_mangled_string_aux i (r.push c))
 <|> (do c ← digit, parse_mangled_string_aux i (r.push c))
 <|> (do str "__", parse_mangled_string_aux i (r.push '_'))
 <|> (do str "_x", d₂ ← parse_hex_digit, d₁ ← parse_hex_digit,
         parse_mangled_string_aux i (r.push (char.of_nat (d₂ * 16 + d₁))))
 <|> (do str "_u", d₄ ← parse_hex_digit, d₃ ← parse_hex_digit, d₂ ← parse_hex_digit, d₁ ← parse_hex_digit,
         parse_mangled_string_aux i (r.push (char.of_nat (d₄ * 4096 + d₃ * 256 + d₂ * 16 + d₁))))

private def parse_mangled_string : parsec' string :=
do r ← remaining, parse_mangled_string_aux r ""

def string.demangle (s : string) : option string :=
(parsec.parse parse_mangled_string s).to_option

private def name.mangle_aux (pre : string) : name → string
| name.anonymous       := pre
| (name.mk_string p s) :=
  let r := name.mangle_aux p in
  let m := string.mangle s in
  r ++ "_s" ++ to_string m.length ++ "_" ++ m
| (name.mk_numeral p n) :=
  let r := name.mangle_aux p in
  r ++ "_" ++ to_string n ++ "_"

def name.mangle (n : name) (pre : string := "_l") : string :=
name.mangle_aux pre n

private def parse_mangled_name_aux : nat → name → parsec' name
| 0 r     := pure r
| (i+1) r :=
      (eoi *> pure r)
  <|> (do str "_s", n ← num, ch '_',
          (some s) ← string.demangle <$> take n,
          parse_mangled_name_aux i (r.mk_string s))
  <|> (do ch '_', n ← num, ch '_',
          parse_mangled_name_aux i (r.mk_numeral n))

private def parse_mangled_name (pre : string) : parsec' name :=
do str pre, r ← remaining, parse_mangled_name_aux r name.anonymous

def name.demangle (s : string) (pre : string := "_l") : option name :=
(parsec.parse (parse_mangled_name pre) s).to_option

end lean
