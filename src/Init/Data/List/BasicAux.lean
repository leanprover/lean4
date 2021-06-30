/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.List.Basic
import Init.Util

universe u

namespace List
/- The following functions can't be defined at `Init.Data.List.Basic`, because they depend on `Init.Util`,
   and `Init.Util` depends on `Init.Data.List.Basic`. -/

def get! [Inhabited α] : Nat → List α → α
  | 0,   a::as => a
  | n+1, a::as => get! n as
  | _,   _     => panic! "invalid index"

def get? : Nat → List α → Option α
  | 0,   a::as => some a
  | n+1, a::as => get? n as
  | _,   _     => none

def getD (idx : Nat) (as : List α) (a₀ : α) : α :=
  (as.get? idx).getD a₀

def head! [Inhabited α] : List α → α
  | []   => panic! "empty list"
  | a::_ => a

def head? : List α → Option α
  | []   => none
  | a::_ => some a

def headD : List α → α → α
  | [],   a₀ => a₀
  | a::_, _  => a

def tail! : List α → List α
  | []    => panic! "empty list"
  | a::as => as

def tail? : List α → Option (List α)
  | []    => none
  | a::as => some as

def tailD : List α → List α → List α
  | [],   as₀ => as₀
  | a::as, _  => as

def getLast : ∀ (as : List α), as ≠ [] → α
  | [],       h => absurd rfl h
  | [a],      h => a
  | a::b::as, h => getLast (b::as) (fun h => List.noConfusion h)

def getLast! [Inhabited α] : List α → α
  | []    => panic! "empty list"
  | a::as => getLast (a::as) (fun h => List.noConfusion h)

def getLast? : List α → Option α
  | []    => none
  | a::as => some (getLast (a::as) (fun h => List.noConfusion h))

def getLastD : List α → α → α
  | [],   a₀ => a₀
  | a::as, _ => getLast (a::as) (fun h => List.noConfusion h)

def rotateLeft (xs : List α) (n : Nat := 1) : List α :=
  let len := xs.length
  if len ≤ 1 then
    xs
  else
    let n := n % len
    let b := xs.take n
    let e := xs.drop n
    e ++ b

def rotateRight (xs : List α) (n : Nat := 1) : List α :=
  let len := xs.length
  if len ≤ 1 then
    xs
  else
    let n := len - n % len
    let b := xs.take n
    let e := xs.drop n
    e ++ b

end List
