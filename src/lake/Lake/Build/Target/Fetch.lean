/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Build.Job
import Lake.Config.Monad

namespace Lake

private def BuildKey.fetchCore (self : BuildKey) : FetchM (Job (BuildData self)) := do
  match self with
  | module modName =>
    let some mod ← findModule? modName
      | error s!"invalid target '{self}': module '{modName}' not found in workspace"
    return Job.pure <| toFamily mod
  | package pkgName =>
    let some pkg ← findPackage? pkgName
      | error s!"invalid target '{self}': package '{pkgName}' not found in workspace"
    return Job.pure <| toFamily pkg.toPackage
  | packageTarget pkgName targetName dataKind =>
    let some pkg ← findPackage? pkgName
      | error s!"invalid target '{self}': package '{pkgName}' not found in workspace"
    match dataKind with
    | .anonymous =>
      fetch <| pkg.target targetName
    | `leanLib =>
      let some lib := pkg.findLeanLib? targetName
        | error s!"invalid target '{self}': Lean library '{targetName}' not found in package '{pkgName}'"
      return Job.pure <| toFamily lib
    | `leanExe =>
      let some exe := pkg.findLeanExe? targetName
        | error s!"invalid target '{self}': Lean executable '{targetName}' not found in package '{pkgName}'"
      return Job.pure <| toFamily exe
    | `externLib =>
      let some lib := pkg.findExternLib? targetName
        | error s!"invalid target '{self}': External library '{targetName}' not found in package '{pkgName}'"
      return Job.pure <| toFamily lib
    | _ =>
      error s!"invalid target '{self}': unknown data kind '{dataKind}'"
  | facet target facetName dataKind =>
    let .anonymous := dataKind
      | error s!"invalid target '{self}': facets do not currently support non-anonymous data kinds"
    if h : target.kind.isAnonymous then
      error s!"invalid target '{self}': facet of opaque target kind '{target.kind}'"
    else
      let job ← target.fetchCore
      let job : Job (TargetData target.kind) :=
        cast (by rw [target.data_eq_of_kind h]) job
      match kind_eq:target.kind with
      | `leanLib =>
        let job : Job LeanLib := cast (by simp [kind_eq]) job
        let job ← job.bindM fun lib => fetch (.libraryFacet lib facetName)
        return cast (by simp [kind_eq]) job
      | `leanExe =>
        let `exe := facetName
          | error s!"invalid target '{self}': unknown executable facet '{facetName}'"
        let job : Job LeanExe := cast (by simp [kind_eq]) job
        let job ← job.bindM fun exe => fetch (.leanExe exe)
        return cast (by simp [kind_eq]) job
      | `externLib =>
        let job : Job ExternLib := cast (by simp [kind_eq]) job
        match facetName with
        | `static =>
          let job ← job.bindM fun lib => fetch (.staticExternLib lib)
          return cast (by simp [kind_eq]) job
        | `shared =>
          let job ← job.bindM fun lib => fetch (.sharedExternLib lib)
          return cast (by simp [kind_eq]) job
        | `dynlib =>
          let job ← job.bindM fun lib => fetch (.dynlibExternLib lib)
          return cast (by simp [kind_eq]) job
        | _ =>
          error s!"invalid target '{self}': unknown external library facet '{facetName}'"
      | _ =>
        error s!"invalid target '{self}': unknown data kind '{dataKind}'"

@[inline] protected def BuildKey.fetch
  (self : BuildKey) [FamilyOut BuildData self α] : FetchM (Job α)
:= cast (by simp) self.fetchCore

@[inline] protected def Target.fetch (self : Target α) : FetchM (Job α) := do
 have := self.data_def; self.key.fetch

protected def TargetArray.fetch (self : TargetArray α) : FetchM (Job (Array α)) := do
  Job.collectArray <$> self.mapM (·.fetch)
