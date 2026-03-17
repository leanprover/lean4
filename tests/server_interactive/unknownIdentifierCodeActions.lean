module
--^ waitForILeans

public section

#check Lean.Server.Test.Refs.test1
                                --^ codeAction

example : LeanServerTestRefsTest0
                               --^ codeAction

namespace Lean.Server.Test.Refs
#check Lean.Server.Test.Refs.test1
                                --^ codeAction
end Lean.Server.Test.Refs

namespace Lean.Server.Test.Refs.Foobar
#check Lean.Server.Test.LeanServerTestRefsTest0'
end Lean.Server.Test.Refs.Foobar

open Lean.Server.Test.Refs.Foobar
#check Lean.Server.Test.Refs.test1
                                --^ codeAction

#check Lean.Server.Test.Refs.test
                               --^ codeAction

namespace Lean.Server.Test.Refs.Test1
#check Lean.Server.Test.Refs.Test1
                                --^ codeAction
end Lean.Server.Test.Refs.Test1


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

def pubNonExposed : Lean.Server.Test.Refs.Test1
                                             --^ codeAction
  := Lean.Server.Test.Refs.Test1
                              --^ codeAction

public meta def pubMeta : Lean.Server.Test.Refs.Test1
                                                   --^ codeAction
  := Lean.Server.Test.Refs.Test1
                              --^ codeAction
