import Lake
open Lake DSL

package test_meta

#print "lorem"

meta if get_config? baz |>.isSome then #print "baz"

meta if get_config? env = some "foo" then do
  #print "foo"
  #print "1"
else meta if get_config? env = some "bar" then do
  #print "bar"
  #print "2"

#print "ipsum"
