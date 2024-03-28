import Lake
open System Lake DSL

package test

@[test_runner]
lean_exe testExe

@[test_runner]
script testScript do return 1
