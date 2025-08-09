/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Build.Trace

open System

namespace Lake

/-- A file with a known content hash. -/
public structure Artifact where
  /-- The path to the artifact on the file system. -/
  path : FilePath
  /-- The name of the artifact. This is used, for example, as a caption in traces. -/
  name := path.toString
  /-- The modification time of the artifact (or `0` if unknown). -/
  mtime : MTime
  /-- The content hash of the artifact. -/
  hash : Hash
  deriving Inhabited, Repr

namespace Artifact

/-- Sets the `name` of the artifact. -/
@[inline] public def withName (name : String) (self : Artifact) : Artifact :=
  {self with name := name}

/-- Sets the `name` and `path` of the artifact using the file outside the Lake artifact cache. -/
@[inline] public def useLocalFile (path : FilePath) (self : Artifact) : Artifact :=
  {self with name := path.toString, path}

/--The build trace formed from this single artifact. -/
public def trace (self : Artifact) : BuildTrace :=
  {caption := self.name, mtime := self.mtime, hash := self.hash}
