class Foo where

class Bar extends Foo where
  bar : True

def foo : Foo := {}

example [Bar] : Bar := {
  foo with bar := by {
    rename_i inst
    guard_hyp inst : Bar
    trivial
  }
}
