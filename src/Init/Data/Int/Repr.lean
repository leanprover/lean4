/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
module

prelude
public import Init.Data.Repr
public import Init.Data.String.Defs

namespace Int

/--
Returns the decimal string representation of an integer.
-/
public protected def repr : Int → String
  | ofNat m   => Nat.repr m
  | negSucc m => "-" ++ Nat.repr (Nat.succ m)

public instance : Repr Int where
  reprPrec i prec := if i < 0 then Repr.addAppParen i.repr prec else i.repr

end Int
