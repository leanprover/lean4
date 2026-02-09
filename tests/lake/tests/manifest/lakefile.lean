import Lake
open Lake DSL

package "foo-bar"

require foo from "foo"
require "foo" / bar from git "bar"
