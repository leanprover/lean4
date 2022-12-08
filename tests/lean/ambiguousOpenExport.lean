inductive Foo.C where
  | mk

inductive Bla.C where
  | mk

open Foo Bla

open C (mk) -- Error

export C (mk) -- Error
