/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Name

namespace Lake

/-- The type of keys in the Lake build store. -/
structure BuildKey where
  package? : Option WfName
  target? : Option WfName
  facet : WfName
  deriving Inhabited, Repr, DecidableEq, Hashable

namespace BuildKey

@[inline] def hasPackage (self : BuildKey) : Bool :=
  self.package? ≠ none

@[simp] theorem hasPackage_mk : BuildKey.hasPackage ⟨some p, x, f⟩ := by
  simp [BuildKey.hasPackage]

@[inline] def package (self : BuildKey) (h : self.hasPackage) : WfName :=
  match mh:self.package? with
  | some n => n
  | none => absurd mh <| by
    unfold hasPackage at h
    exact of_decide_eq_true h

@[inline] def hasTarget (self : BuildKey) : Bool :=
  self.target? ≠ none

@[simp] theorem hasTarget_mk : BuildKey.hasTarget ⟨x, some t, f⟩ := by
  simp [BuildKey.hasTarget]

@[inline] def target (self : BuildKey) (h : self.hasTarget) : WfName :=
  match mh:self.target? with
  | some n => n
  | none => absurd mh <| by
    unfold hasTarget at h
    exact of_decide_eq_true h

@[inline] def isModuleKey (self : BuildKey) : Bool :=
  self.package? = none ∧ self.hasTarget

@[simp] theorem isModuleKey_mk : BuildKey.isModuleKey ⟨none, some m, f⟩ := by
  simp [BuildKey.isModuleKey]

@[simp] theorem not_isModuleKey_pkg : ¬BuildKey.isModuleKey ⟨some pkg, x, f⟩ := by
  simp [BuildKey.isModuleKey]

@[inline] def module (self : BuildKey) (h : self.isModuleKey) : WfName :=
  self.target <| by
    unfold isModuleKey at h
    exact of_decide_eq_true h |>.2

@[inline] def isPackageKey (self : BuildKey) : Bool :=
  self.hasPackage ∧ self.target? = none

@[simp] theorem isPackageKey_mk : BuildKey.isPackageKey ⟨some p, none, f⟩ := by
  simp [BuildKey.isPackageKey]

@[inline] def isTargetKey (self : BuildKey) : Bool :=
  self.hasPackage ∧ self.hasTarget

@[simp] theorem isTargetKey_mk : BuildKey.isTargetKey ⟨some p, some t, f⟩ := by
  simp [BuildKey.isTargetKey]

protected def toString : (self : BuildKey) → String
| ⟨some p,  none,   f⟩ => s!"@{p}:{f}"
| ⟨none,    some m, f⟩ => s!"+{m}:{f}"
| ⟨some p,  some t, f⟩ => s!"{p}/{t}:{f}"
| ⟨none,    none,   f⟩ => s!":{f}"

instance : ToString BuildKey := ⟨(·.toString)⟩

def quickCmp (k k' : BuildKey) :=
  match Option.compareWith WfName.quickCmp k.package? k'.package? with
  | .eq =>
    match Option.compareWith WfName.quickCmp k.target? k'.target? with
    | .eq => k.facet.quickCmp k'.facet
    | ord => ord
  | ord => ord

theorem eq_of_quickCmp :
{k k' : _} → quickCmp k k' = Ordering.eq → k = k' := by
  intro ⟨p, t, f⟩ ⟨p', t', f'⟩
  unfold quickCmp
  simp only []
  split
  next p_eq =>
    split
    next t_eq =>
      intro f_eq
      have p_eq := eq_of_cmp p_eq
      have t_eq := eq_of_cmp t_eq
      have f_eq := eq_of_cmp f_eq
      simp only [p_eq, t_eq, f_eq]
    next =>
      intros; contradiction
  next =>
    intros; contradiction

instance : EqOfCmp BuildKey quickCmp where
  eq_of_cmp := eq_of_quickCmp

end BuildKey

-- ## Subtypes

/-- The type of build keys for modules. -/
structure ModuleBuildKey (fixedFacet : WfName) extends BuildKey where
  is_module_key : toBuildKey.isModuleKey = true
  facet_eq_fixed : toBuildKey.facet = fixedFacet

instance : Coe (ModuleBuildKey f) BuildKey := ⟨(·.toBuildKey)⟩

@[inline] def BuildKey.toModuleKey
(self : BuildKey) (h : self.isModuleKey) : ModuleBuildKey self.facet :=
  ⟨self, h, rfl⟩

@[inline] def ModuleBuildKey.module (self : ModuleBuildKey f) : WfName :=
  self.toBuildKey.module self.is_module_key

/-- The type of build keys for packages. -/
structure PackageBuildKey (fixedFacet : WfName) extends BuildKey where
  is_package_key : toBuildKey.isPackageKey = true
  facet_eq_fixed : toBuildKey.facet = fixedFacet

instance : Coe (PackageBuildKey f) BuildKey := ⟨(·.toBuildKey)⟩

@[inline] def BuildKey.toPackageKey
(self : BuildKey) (h : self.isPackageKey) : PackageBuildKey self.facet :=
  ⟨self, h, rfl⟩

@[inline] def PackageBuildKey.package (self : PackageBuildKey f) : WfName :=
  self.toBuildKey.package <| by
    have h := self.is_package_key
    unfold BuildKey.isPackageKey at h
    exact (of_decide_eq_true h).1
