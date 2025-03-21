/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Build.Job
import Lake.Config.Monad

namespace Lake

protected def BuildKey.fetch (self : BuildKey) [h : FamilyOut BuildData self α] : FetchM (Job α) := do
  match self_eq:self with
  | moduleFacet modName facetName =>
    let some mod ← findModule? modName
      | error s!"invalid target '{self}': module '{modName}' not found in workspace"
    have : FamilyOut BuildData (mod.facet facetName).key α :=
      ⟨by simpa [self_eq] using h.family_key_eq_type⟩
    fetch <| mod.facet facetName
  | packageFacet pkgName facetName =>
    let some pkg ← findPackage? pkgName
      | error s!"invalid target '{self}': package '{pkgName}' not found in workspace"
    have : FamilyOut BuildData (pkg.facet facetName).key α :=
      ⟨by simpa [self_eq] using h.family_key_eq_type⟩
    fetch <| pkg.facet facetName
  | targetFacet pkgName targetName facetName =>
    -- TODO: Support this
    error s!"unsupported target {self}: fetching builtin targets by key is not currently supported"
  | customTarget pkgName targetName =>
    let some pkg ← findPackage? pkgName
      | error s!"invalid target '{self}': package '{pkgName}' not found in workspace"
    have : FamilyOut BuildData (pkg.target targetName).key α :=
      ⟨by simpa [self_eq] using h.family_key_eq_type⟩
    fetch <| pkg.target targetName

@[inline] protected def Target.fetch (self : Target α) : FetchM (Job α) := do
 have := self.data_def; self.key.fetch

protected def TargetArray.fetch (self : TargetArray α) : FetchM (Job (Array α)) := do
  Job.collectArray <$> self.mapM (·.fetch)
