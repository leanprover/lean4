/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lake.Load.Main
import Lake.Util.MainM

/-!
# Data structures for `dump-config`
-/

open Lean

namespace Lake

structure WorkspaceExport where
  version := 1
  root : Name
  packages : Array Package
  env : Env
  deriving ToJson

def Workspace.toExport (ws : Workspace) : WorkspaceExport where
  root := ws.root.name
  env := ws.lakeEnv
  packages := ws.packages
