/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Init.Data.ToString.Basic
import all Init.Data.String.Extra

namespace Lake

public def lpad (s : String) (c : Char) (len : Nat) : String :=
  "".pushn c (len - s.length) ++ s

public def rpad (s : String) (c : Char) (len : Nat) : String :=
  s.pushn c (len - s.length)

public def zpad (n : Nat) (len : Nat) : String :=
  lpad (toString n) '0' len
