open Lean in
macro "tst" : term => do
  Macro.trace[Meta.debug] "macro tst executed"
  `(0)

#check tst

set_option trace.Meta.debug true in
#check tst

open Lean in
macro "tstcmd" : command => do
  Macro.trace[Meta.debug] "macro cmdtst executed {1+2}"
  `(#print "hello")

tstcmd

set_option trace.Meta.debug true in
tstcmd
