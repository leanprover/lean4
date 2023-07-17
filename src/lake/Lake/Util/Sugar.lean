/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
namespace Lake

macro "try " x:term " else " y:term : term =>
  ``($x <|> $y)

macro "try " x:doSeq " else " y:doSeq : doElem =>
  `(doElem| (do $x) <|> (do $y))
