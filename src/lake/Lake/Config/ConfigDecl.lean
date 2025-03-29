/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Config.Opaque
import Lake.Config.LeanLibConfig
import Lake.Config.LeanExeConfig
import Lake.Config.ExternLibConfig
import Lake.Config.InputFileConfig

open Lean (Name)

namespace Lake

abbrev ConfigType (kind : Name) (pkgName name : Name) : Type :=
  match kind with
  | LeanLib.configKind => LeanLibConfig name
  | LeanExe.configKind => LeanExeConfig name
  | ExternLib.configKind => ExternLibConfig pkgName name
  | .anonymous => OpaqueTargetConfig pkgName name
  | InputFile.configKind => InputFileConfig name
  | InputDir.configKind => InputDirConfig name
  | _ => Empty

/-- Forward declared `ConfigTarget` to work around recursion issues (e.g., with `Package`). -/
opaque OpaqueConfigTarget (kind : Name) : Type

structure ConfigDecl where
  pkg : Name
  name : Name
  kind : Name
  config : ConfigType kind pkg name
  wf_data : ¬ kind.isAnonymous → CustomData pkg name = DataType kind ∧ DataType kind = OpaqueConfigTarget kind
  deriving TypeName

structure PConfigDecl (p : Name) extends ConfigDecl where
  pkg_eq : toConfigDecl.pkg = p := by rfl

structure NConfigDecl (p n : Name) extends PConfigDecl p where
  name_eq : toConfigDecl.name = n := by rfl

structure KConfigDecl (k : Name) extends ConfigDecl where
  kind_eq : toConfigDecl.kind = k := by rfl

instance : Nonempty (NConfigDecl pkg name) :=
  ⟨{pkg, name, kind := .anonymous, config := Classical.ofNonempty, wf_data := by simp [Name.isAnonymous]}⟩

@[inline] def ConfigDecl.partialKey (self : ConfigDecl) : PartialBuildKey :=
  .packageTarget .anonymous self.name

instance : CoeOut (KConfigDecl k) PartialBuildKey := ⟨(·.partialKey)⟩

@[inline] def PConfigDecl.config' (self : PConfigDecl p) : ConfigType self.kind p self.name :=
  cast (by rw [self.pkg_eq]) self.config

@[inline] def NConfigDecl.config' (self : NConfigDecl p n) : ConfigType self.kind p n :=
  cast (by rw [self.name_eq]) self.toPConfigDecl.config'

theorem NConfigDecl.target_eq_type (self : NConfigDecl p n)
  (h : ¬ self.kind.isAnonymous) : DataType self.kind = OpaqueConfigTarget self.kind
:= self.wf_data h |>.2

theorem NConfigDecl.data_eq_target (self : NConfigDecl p n)
  (h : ¬ self.kind.isAnonymous) : CustomData p n = OpaqueConfigTarget self.kind
:= by simpa [self.pkg_eq, self.name_eq, self.target_eq_type h] using (self.wf_data h).1

@[inline] def ConfigDecl.config? (kind : Name) (self : ConfigDecl) : Option (ConfigType kind self.pkg self.name) :=
  if h : self.kind = kind then
    some <| cast (by rw [h]) self.config
  else
    none

@[inline] def PConfigDecl.config? (kind : Name) (self : PConfigDecl p) : Option (ConfigType kind p self.name) :=
  cast (by rw [self.pkg_eq]) (self.toConfigDecl.config? kind)

@[inline] def NConfigDecl.config? (kind : Name) (self : NConfigDecl p n) : Option (ConfigType kind p n) :=
  cast (by rw [self.name_eq]) (self.toPConfigDecl.config? kind)

@[inline] def ConfigDecl.leanLibConfig? (self : ConfigDecl) : Option (LeanLibConfig self.name) :=
  self.config? LeanLib.configKind

@[inline] def NConfigDecl.leanLibConfig? (self : NConfigDecl p n) : Option (LeanLibConfig n) :=
  self.config? LeanLib.configKind

/-- A Lean library declaration from a configuration written in Lean. -/
abbrev LeanLibDecl := KConfigDecl LeanLib.configKind

@[inline] def ConfigDecl.leanExeConfig? (self : ConfigDecl) : Option (LeanExeConfig self.name) :=
  self.config? LeanExe.configKind

@[inline] def NConfigDecl.leanExeConfig? (self : NConfigDecl p n) : Option (LeanExeConfig n) :=
  self.config? LeanExe.configKind

/-- A Lean executable declaration from a configuration written in Lean. -/
abbrev LeanExeDecl := KConfigDecl LeanExe.configKind

@[inline] def PConfigDecl.externLibConfig? (self : PConfigDecl p) : Option (ExternLibConfig p self.name) :=
  self.config? ExternLib.configKind

@[inline] def NConfigDecl.externLibConfig? (self : NConfigDecl p n) : Option (ExternLibConfig p n) :=
  self.config? ExternLib.configKind

/-- An external library declaration from a configuration written in Lean. -/
abbrev ExternLibDecl := KConfigDecl ExternLib.configKind

@[inline] def PConfigDecl.opaqueTargetConfig (self : PConfigDecl p) (h : self.kind.isAnonymous) : OpaqueTargetConfig p self.name :=
  cast (by rw [self.pkg_eq, Name.eq_anonymous_of_isAnonymous h, ConfigType]) self.config

@[inline] def NConfigDecl.opaqueTargetConfig (self : NConfigDecl p n) (h : self.kind.isAnonymous) : OpaqueTargetConfig p n :=
  cast (by rw [self.name_eq]) (self.toPConfigDecl.opaqueTargetConfig h)

@[inline] def PConfigDecl.opaqueTargetConfig? (self : PConfigDecl p) : Option (OpaqueTargetConfig p self.name) :=
  if h : self.kind.isAnonymous then
    some <| self.opaqueTargetConfig h
  else
    none

@[inline] def NConfigDecl.opaqueTargetConfig? (self : NConfigDecl p n) : Option (OpaqueTargetConfig p n) :=
  cast (by rw [self.name_eq]) self.toPConfigDecl.opaqueTargetConfig?

/-- A input file declaration from a configuration written in Lean. -/
abbrev InputFileDecl := KConfigDecl InputFile.configKind

/-- A inpurt directory declaration from a configuration written in Lean. -/
abbrev InputDirDecl := KConfigDecl InputDir.configKind

deriving instance TypeName for
  LeanLibDecl, LeanExeDecl,
  InputFileDecl, InputDirDecl
