--^ waitForILeans
module

-- Regression test for a bug where the module system broke the call hierarchy when tracking it
-- through a `where` in a `public def` of a `module`.

public section

def f := 0
   --^ incomingCallHierarchy

def foo : Nat :=
  bar
where
  bar : Nat := f

def foobar := foo
