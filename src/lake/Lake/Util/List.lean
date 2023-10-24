/-
Copyright (c) 2023 Siddharth Bhat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat
-/

open Lean

namespace Lake

/-- Remove adjacent duplicates. -/
def List.squeeze [BEq α] : List α → List α
| [] => []
| x :: xs =>
  match List.squeeze xs with
  | [] => [x]
  | x' :: xs' => if x == x' then x' :: xs' else x :: x' :: xs'

end Lake
