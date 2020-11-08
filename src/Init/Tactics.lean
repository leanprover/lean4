/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.LeanInit
import Init.Data.Array.Macros

macro "rfl" : tactic => `(exact rfl)
macro "decide!" : tactic => `(exact decide!)
macro "admit" : tactic => `(exact sorry)
/- We use a priority > 0, to avoid ambiguity with the builtin `have` notation -/
macro[1] "have" x:ident ":=" p:term : tactic => `(have $x:ident : _ := $p)

syntax "repeat " tacticSeq : tactic

macro_rules
  | `(tactic| repeat $seq) => `(tactic| (($seq); repeat $seq) <|> skip)

macro "try " t:tacticSeq : tactic => `(($t) <|> skip)

syntax "funext " (>col term:max)+ : tactic

macro_rules
  | `(tactic|funext $xs*) =>
    if xs.size == 1 then
      `(tactic| apply funext; intro $(xs[0]):term)
    else
      `(tactic| apply funext; intro $(xs[0]):term; funext $(xs[1:])*)
