/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

namespace Lake

/-- This is the same as `String.replace text "\r\n" "\n"`, but more efficient. -/
@[inline] partial def crlf2lf (text : String) : String :=
  go "" 0 0
where
  go (acc : String) (accStop pos : String.Pos) : String :=
    if h : text.atEnd pos then
      -- note: if accStop = 0 then acc is empty
      if accStop = 0 then text else acc ++ text.extract accStop pos
    else
      let c := text.get' pos h
      let pos' := text.next' pos h
      if c == '\r' && text.get pos' == '\n' then
        let acc := acc ++ text.extract accStop pos
        go acc pos' (text.next pos')
      else
        go acc accStop pos'
