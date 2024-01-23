import Lake
open Lake DSL

package test

require leanprover / Cli
  from github "leanprover" / "lean4-cli"

--TODO: does not work due to name mismatch
--require leanprover / std4 @ "main"

require "leanprover-community" / "aesop"

#eval leanprover.Cli.fullName
