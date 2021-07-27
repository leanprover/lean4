open Nat in
macro "foo" : command => `(
  #check zero
  #check ``succ)

foo

macro "bar" : command => `(
  #check zero
  #check ``succ)

open Nat in
bar
