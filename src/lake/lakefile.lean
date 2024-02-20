/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.DSL
open System Lake DSL

package lake

lean_lib Lake

@[default_target]
lean_exe lake where
  root := `Lake.Main
  supportInterpreter := true
