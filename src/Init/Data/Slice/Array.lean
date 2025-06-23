module

prelude
import Init.Core
import Init.Data.Slice.Basic

open Std.Slice

instance {shape} {α : Type u} : Sliceable shape (Array α) Nat where

instance : SliceIter ⟨.closed, .open⟩ (Array α) where
  State := _
