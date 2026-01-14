import Lean

macro "t" t:interpolatedStr(term) : doElem =>
  `(doElem| Macro.trace[Meta.debug] $t)

macro "tstcmd" : command => do
  t "hello"
  `(example : Nat := 1)

set_option trace.Meta.debug true in
tstcmd

open Lean Meta

macro "r" r:interpolatedStr(term) : doElem =>
  `(doElem| trace[Meta.debug] $r)

set_option trace.Meta.debug true in
#eval show MetaM _ from do r "world"
