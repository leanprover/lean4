/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mac Malone
-/
module

prelude
public import Init

namespace Lean

/--
The type of module package identifiers.

This is a {name}`String` that is used to disambiguate identifiers
(e.g. native symbol prefixes or .ilean files) between
different packages (and different versions of the same package).
-/
public abbrev PkgId := String

/--
Versioned variant of `PkgId`.
When multi-version workspaces are enabled, a workspace can include multiple versions of the same
package, while versions are still unique in the dependency closure of any single package.
Hence, tooling that can see the entire workspace at once (e.g. the language server) needs to be able
to distinguish between different versions of the same package.
-/
public abbrev VersionedPkgId := String

/--
Dedicated identifier for core, either as a dependency (that all packages include) or for the
package itself while working on core.
-/
public abbrev VersionedPkgId.core : Lean.VersionedPkgId := "core"

/--
Module name augmented with the `VersionedPkgId` it is contained in. Allows uniquely identifying
modules in a global (workspace) setting, e.g. the language server.

The `VersionedPkgId` can be `none` if the module name is not contained in a package
(e.g. if it is a scratch file).
-/
public structure GlobalModId where
  /--
  Package that this module is in.
  Can be `none` if the module name is not contained in a package
  (e.g. if it is a scratch file).
  -/
  pkg? : Option VersionedPkgId
  /--
  Module name that this identifier is referring to.
  Note that when multi-version workspaces are enabled,
  `mod` on its own only uniquely identifies a module in the dependency closure of a
  specific package.
  -/
  mod  : Name
  deriving Inhabited, Repr
