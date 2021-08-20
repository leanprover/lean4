/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Target
import Lake.BuildMonad

open System
namespace Lake

--------------------------------------------------------------------------------
-- # Build Targets
--------------------------------------------------------------------------------

-- ## Inactive Target

abbrev BuildTarget a :=
  Target LakeTrace BuildM a

namespace BuildTarget

def nil : BuildTarget PUnit :=
  Target.pure () LakeTrace.nil

def hash (self : BuildTarget a) := self.trace.hash
def mtime (self : BuildTarget a) := self.trace.mtime

end BuildTarget

-- ## Active Target

abbrev ActiveBuildTarget a :=
  ActiveTarget LakeTrace BuildTask a

namespace ActiveBuildTarget

def nil : ActiveBuildTarget PUnit :=
  ActiveTarget.pure () LakeTrace.nil

def hash (self : ActiveBuildTarget a) := self.trace.hash
def mtime (self : ActiveBuildTarget a) := self.trace.mtime

end ActiveBuildTarget

--------------------------------------------------------------------------------
-- # File Targets
--------------------------------------------------------------------------------

-- ## File Target

abbrev FileTarget :=
  BuildTarget FilePath

namespace FileTarget

def compute (file : FilePath) : IO FileTarget :=
  Target.compute file

end FileTarget

-- ## Active File Target

abbrev ActiveFileTarget :=
  ActiveBuildTarget FilePath
