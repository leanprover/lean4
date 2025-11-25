import Lean.Server.Test.Refs
--^ waitForILeans

def foo := 0
   --^ incomingCallHierarchy

def bar1 := foo
def bar2 := foo

def foobar : Lean.Server.Test.Refs.Test1 := sorry
              --^ incomingCallHierarchy
def barfoo := foobar
