/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Config.Context
import Lake.Build.Job.Basic

open System
namespace Lake

/-- Configuration options for a Lake build. -/
structure BuildConfig where
  /-- Use modification times for trace checking. -/
  oldMode : Bool := false
  /-- Whether to trust `.hash` files. -/
  trustHash : Bool := true
  /-- Early exit if a target has to be rebuilt. -/
  noBuild : Bool := false
  /-- Verbosity level (`-q`, `-v`, or neither). -/
  verbosity : Verbosity := .normal
  /--
  Fail the top-level build if entries of at least this level have been logged.

  Unlike some build systems, this does **NOT** convert such log entries to
  errors, and it does not abort jobs when warnings are logged (i.e.,
  dependent jobs will still continue unimpeded).
  -/
  failLv : LogLevel := .error
  /-- The minimum log level for an log entry to be reported. -/
  outLv : LogLevel := verbosity.minLogLv
  /--
  The stream to which Lake reports build progress.
  By default, Lake uses `stderr`.
  -/
  out : OutStream := .stderr
  /-- Whether to use ANSI escape codes in build output. -/
  ansiMode : AnsiMode := .auto

/--
Whether the build should show progress information.

`Verbosity.quiet` hides progress and, for a `noBuild`,
`Verbosity.verbose` shows progress.
-/
def BuildConfig.showProgress (cfg : BuildConfig) : Bool :=
  (cfg.noBuild ∧ cfg.verbosity == .verbose) ∨ cfg.verbosity != .quiet

/-- A Lake context with a build configuration and additional build data. -/
structure BuildContext extends BuildConfig, Context where
  leanTrace : BuildTrace
  registeredJobs : IO.Ref (Array OpaqueJob)

/-- A transformer to equip a monad with a `BuildContext`. -/
abbrev BuildT := ReaderT BuildContext

/-- A monad equipped with a Lake build context. -/
abbrev MonadBuild (m : Type → Type u) :=
  MonadReaderOf BuildContext m

instance [Pure m] : MonadLift LakeM (BuildT m) where
  monadLift x := fun ctx => pure <| x.run ctx.toContext

@[inline] def getBuildContext [MonadBuild m] : m BuildContext :=
  readThe BuildContext

@[inline] def getLeanTrace [Functor m] [MonadBuild m] : m BuildTrace :=
  (·.leanTrace) <$> getBuildContext

@[inline] def getBuildConfig [Functor m] [MonadBuild m] : m BuildConfig :=
  (·.toBuildConfig) <$> getBuildContext

@[inline] def getIsOldMode [Functor m] [MonadBuild m] : m Bool :=
  (·.oldMode) <$> getBuildConfig

@[inline] def getTrustHash [Functor m] [MonadBuild m] : m Bool :=
  (·.trustHash) <$> getBuildConfig

@[inline] def getNoBuild [Functor m] [MonadBuild m] : m Bool :=
  (·.noBuild) <$> getBuildConfig

@[inline] def getVerbosity [Functor m] [MonadBuild m] : m Verbosity :=
  (·.verbosity) <$> getBuildConfig

@[inline] def getIsVerbose [Functor m] [MonadBuild m] : m Bool :=
  (· == .verbose) <$> getVerbosity

@[inline] def getIsQuiet [Functor m] [MonadBuild m] : m Bool :=
  (· == .quiet) <$> getVerbosity
