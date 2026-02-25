import Lean.Server.Test.Refs
--^ waitForILeans

inductive Unit' where
  | mk

inductive Sum' (α β) where
  | left (a : α)
  | right (b : β)

def foo : Unit' := .mk
def bar := foo
def foobar (s : Sum' α β) : Unit' :=
  match s with
  | .left _ => foo
  | .right _ => bar
def barfoo (s : Sum' α β) := foobar s
                                   --^ outgoingCallHierarchy

def test12 (_ : Lean.Server.Test.Refs.Test6) : Unit' := .mk

def test11 (s : Sum' α β) : Unit' :=
  match s with
  | .left _ => barfoo s
  | .right _ => test12 Lean.Server.Test.Refs.test10

def test13 (s : Sum' α β) := test11 s
                                   --^ outgoingCallHierarchy
