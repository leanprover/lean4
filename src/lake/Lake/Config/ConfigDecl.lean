/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Config.Opaque
import Lake.Config.LeanLibConfig
import Lake.Config.LeanExeConfig
import Lake.Config.ExternLibConfig

open Lean (Name)

namespace Lake

abbrev ConfigType (kind : Name) (pkgName name : Name) : Type :=
  match kind with
  | `leanLib => LeanLibConfig name
  | `leanExe => LeanExeConfig name
  | `externLib => ExternLibConfig pkgName name
  | .anonymous => OpaqueTargetConfig pkgName name
  | _ => Empty

structure ConfigDecl where
  pkg : Name
  name : Name
  kind : Name
  config : ConfigType kind pkg name
  deriving TypeName

structure PConfigDecl (p : Name) extends ConfigDecl where
  pkg_eq : toConfigDecl.pkg = p

structure NConfigDecl (p n : Name) extends PConfigDecl p where
  name_eq : toConfigDecl.name = n

structure KConfigDecl (k : Name) extends ConfigDecl where
  kind_eq : toConfigDecl.kind = k

@[inline] def ConfigDecl.config? (kind : Name) (self : ConfigDecl) : Option (ConfigType kind self.pkg self.name) :=
  if h : self.kind = kind then
    some <| cast (by simp [h]) self.config
  else
    none

@[inline] def PConfigDecl.config? (kind : Name) (self : PConfigDecl p) : Option (ConfigType kind p self.name) :=
  cast (by simp [self.pkg_eq]) (self.toConfigDecl.config? kind)

@[inline] def NConfigDecl.config? (kind : Name) (self : NConfigDecl p n) : Option (ConfigType kind p n) :=
  cast (by simp [self.name_eq]) (self.toPConfigDecl.config? kind)

@[inline] def ConfigDecl.leanLibConfig? (self : ConfigDecl) : Option (LeanLibConfig self.name) :=
  self.config? LeanLib.KIND

@[inline] def NConfigDecl.leanLibConfig? (self : NConfigDecl p n) : Option (LeanLibConfig n) :=
  self.config? LeanLib.KIND

/-- A  Lean library declaration from a configuration written in Lean. -/
abbrev LeanLibDecl := KConfigDecl LeanLib.KIND

@[inline] def ConfigDecl.leanExeConfig? (self : ConfigDecl) : Option (LeanExeConfig self.name) :=
  self.config? LeanExe.KIND

@[inline] def NConfigDecl.leanExeConfig? (self : NConfigDecl p n) : Option (LeanExeConfig n) :=
  self.config? LeanExe.KIND

/-- A Lean executable declaration from a configuration written in Lean. -/
abbrev LeanExeDecl := KConfigDecl LeanExe.KIND

@[inline] def PConfigDecl.externLibConfig? (self : PConfigDecl p) : Option (ExternLibConfig p self.name) :=
  self.config? ExternLib.KIND

@[inline] def NConfigDecl.externLibConfig? (self : NConfigDecl p n) : Option (ExternLibConfig p n) :=
  self.config? ExternLib.KIND

/-- An external library declaration from a configuration written in Lean. -/
abbrev ExternLibDecl := KConfigDecl ExternLib.KIND

@[inline] def PConfigDecl.opaqueTargetConfig? (self : PConfigDecl p) : Option (OpaqueTargetConfig p self.name) :=
  if h : self.kind.isAnonymous then
    have h : self.kind = .anonymous := by
      revert h; cases self.kind <;> simp [Name.isAnonymous]
    some <| cast (by simp [self.pkg_eq, h, ConfigType]) self.config
  else
    none

@[inline] def NConfigDecl.opaqueTargetConfig? (self : NConfigDecl p n) : Option (OpaqueTargetConfig p n) :=
  cast (by simp [self.name_eq]) self.toPConfigDecl.opaqueTargetConfig?

deriving instance TypeName for LeanLibDecl, LeanExeDecl
