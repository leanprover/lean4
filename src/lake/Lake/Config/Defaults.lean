/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Init.System.FilePath

namespace Lake

open System (FilePath)

/--
The default directory to output Lake-related files
(e.g., build artifacts, packages, caches, etc.).
Currently not configurable.
-/
public def defaultLakeDir : FilePath := ".lake"

/-- The default setting for a `WorkspaceConfig`'s `packagesDir` option. -/
public def defaultPackagesDir := defaultLakeDir / "packages"

/-- The default name of the Lake configuration file (i.e., `lakefile`). -/
public def defaultConfigFile : FilePath := "lakefile"

/-- The default name of the Lean Lake configuration file (i.e., `lakefile.lean`). -/
public def defaultLeanConfigFile : FilePath := defaultConfigFile |>.addExtension "lean"

/-- The default name of the TOML Lake configuration file (i.e., `lakefile.toml`). -/
public def defaultTomlConfigFile : FilePath := defaultConfigFile |>.addExtension "toml"

/-- The default name of the Lake manifest file (i.e., `lake-manifest.json`). -/
public def defaultManifestFile : FilePath := "lake-manifest.json"

/-- The default build directory for packages (i.e., `.lake/build`). -/
public def defaultBuildDir : FilePath := defaultLakeDir / "build"

/-- The default Lean library directory for packages. -/
public def defaultLeanLibDir : FilePath := "lib" / "lean"

/-- The default native library directory for packages. -/
public def defaultNativeLibDir : FilePath := "lib"

/-- The default binary directory for packages. -/
public def defaultBinDir : FilePath := "bin"

/-- The default IR directory for packages. -/
public def defaultIrDir : FilePath := "ir"
