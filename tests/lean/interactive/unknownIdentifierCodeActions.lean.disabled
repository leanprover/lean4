--^ waitForILeans
#check Lean.Server.Test.Refs.test1
                                --^ codeAction

example : LeanServerTestRefsTest0
                               --^ codeAction

#check Lean.Server.Test.Refs.test
                               --^ codeAction

structure Foobar where
  veryLongAndHopefullyVeryUniqueBar0 : Nat

namespace Foobar

def veryLongAndHopefullyVeryUniqueFoo0 := 0

def veryLongAndHopefullyVeryUniqueFoobar0 : Foobar := { veryLongAndHopefullyVeryUniqueBar0 := 0 }

end Foobar

open Foobar

#check veryLongAndHopefullyVeryUniqueFoo
                                      --^ codeAction

example (f : Foobar) : Nat := f.veryLongAndHopefullyVeryUniqueBar
                                                               --^ codeAction

example : Foobar := .veryLongAndHopefullyVeryUniqueFoobar
                                                       --^ codeAction
