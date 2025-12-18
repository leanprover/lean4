import Lake
open Lake DSL

package test_meta

def test_run_io : Unit :=
  run_io IO.println "impure"

meta if get_config? baz |>.isSome then #print "baz"

meta if get_config? env = some "foo" then do
  #print "foo"
  #print "lorem"
else meta if get_config? env = some "bar" then do
  #print "bar"
  #print "ipsum"

script print_env do
  IO.eprintln <| get_config? env |>.getD "none"
  return 0

elab "elab_str" : term => do
  return Lean.toExpr "elabbed-string"

script print_elab do
  IO.eprintln elab_str
  return 0
