import Lake
open System Lake DSL

package test

meta if get_config? foo |>.isSome then
require "leanprover" / "foo"

require bar from git "bar1"
