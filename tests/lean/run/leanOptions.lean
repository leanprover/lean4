import Lean.Util.LeanOptions

open Lean

#guard (LeanOptionValue.ofString "two words").asCliFlagValue == "two words"
#guard (LeanOption.mk `example (.ofString "two words")).asCliArg == "-Dexample=two words"
