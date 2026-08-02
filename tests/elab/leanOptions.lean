import Lean.Util.LeanOptions

/-!
String-valued Lean options are passed as direct subprocess arguments, so their CLI values must not
contain shell quotes.
-/

open Lean

#guard (LeanOptionValue.ofString "two words").asCliFlagValue == "two words"
#guard (LeanOption.mk `example (.ofString "two words")).asCliArg == "-Dexample=two words"
