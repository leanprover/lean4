import Lake
open Lake DSL

package test

require dep from git "dep" @ "release"

lean_lib Test
