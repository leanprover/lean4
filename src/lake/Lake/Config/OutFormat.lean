/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Build.Job

open Lean

namespace Lake

/-- Build output formats supported by the Lake CLI (e.g., `lake fetch`). -/
inductive OutFormat
| /-- Format build output as a raw string. -/ string
| /-- Format build output as JSON. -/ json

/-- Constructs a fetch job that produces no output from a build job. -/
def nullFetchJob (fmt : OutFormat) (data : BuildJob α) : BuildJob String :=
  match fmt with
  | .string => data.map fun _ => ""
  | .json => data.map fun _ => Json.null.compress
