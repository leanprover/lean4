/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Andrew Kent, Leonardo de Moura
-/
module

prelude
public import Init.Data.String.Basic
public import Init.Data.Stream

public instance : Std.Stream Substring.Raw Char where
  next? s :=
    if s.startPos < s.stopPos then
      some (s.startPos.get s.str, { s with startPos := s.startPos.next s.str })
    else
      none
