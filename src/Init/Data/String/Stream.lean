/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Andrew Kent, Leonardo de Moura
-/
module

prelude
public import Init.Data.String.Basic
public import Init.Data.Stream

public instance : Stream Substring Char where
  next? s :=
    if s.startPos < s.stopPos then
      some (s.str.get s.startPos, { s with startPos := s.str.next s.startPos })
    else
      none
