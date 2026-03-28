/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Init.System.FilePath
public import Std.Data.TreeMap.Basic
public import Lean.Data.Name
import Lake.Util.Name
import Init.Data.String.TakeDrop
public import Init.Data.String.Basic
import Init.Data.Option.Coe
import Init.Omega

open System Lean

namespace Lake

/-! ## Match Notation -/

public class IsPattern (α : Type u) (β : outParam $ Type v) where
  /-- Returns whether the value matches the pattern. -/
  satisfies (pat : α) (val : β) : Bool

@[inherit_doc] scoped infix:50 " =~ " => IsPattern.satisfies

/-! ## Abstract Patterns -/

public section -- for `mutual`
mutual

/--
A pattern. Matches some subset of the values of a type.
May also include a declarative description.
-/
public structure Pattern (α : Type u) (β : Type v) where
  /-- Returns whether the value matches the pattern. -/
  filter : α → Bool
   /-- An optional name for the filter. -/
  name := Name.anonymous
  /-- A optional declarative description of the filter. -/
  descr? : Option (PatternDescr α β) := none
  deriving Inhabited

/--
An abstract declarative pattern.
Augments another pattern description `β` with logical connectives.
-/
public inductive PatternDescr (α : Type u) (β : Type v)
/-- Matches a value that does not satisfy the pattern. -/
| not (p : Pattern α β)
/-- Matches a value that satisfies every pattern. Short-circuits. -/
| all (ps : Array (Pattern α β))
/-- Matches a value that satisfies any one of the patterns. Short-circuits. -/
| any (ps : Array (Pattern α β))
/-- Matches a value that satisfies the underlying pattern description. -/
| coe (p : β)
deriving Inhabited

end
end

public instance : Coe β (PatternDescr α β) := ⟨.coe⟩

/-- Returns whether the value matches the pattern. Alias for `filter`. -/
public abbrev Pattern.matches (a : α) (self : Pattern α β) : Bool :=
  self.filter a

public instance : IsPattern (Pattern α β) α := ⟨Pattern.filter⟩

/-- Returns whether the value matches the pattern. -/
@[specialize] public def PatternDescr.matches
  [IsPattern β α] (val : α) (self : PatternDescr α β)
: Bool :=
  match self with
  | .not p => !(p =~ val)
  | .all ps => ps.all (· =~ val)
  | .any ps => ps.any (· =~ val)
  | .coe p => p =~ val

public instance [IsPattern β α] : IsPattern (PatternDescr α β) α := ⟨flip PatternDescr.matches⟩

/--
Matches a value that satisfies an arbitrary predicate
(optionally identified by a `Name`).
-/
@[inline] public def Pattern.ofFn (f : α → Bool) (name := Name.anonymous) : Pattern α β :=
  {filter := f, name}

public instance : Coe (α → Bool) (Pattern α β) := ⟨.ofFn⟩

/--
Matches a string that satisfies the declarative pattern.
(optionally identified by a `Name`).
-/
@[inline] public def Pattern.ofDescr [IsPattern β α] (descr : PatternDescr α β) (name := Name.anonymous) : Pattern α β :=
  {filter := (descr =~ ·), descr? := descr, name}

public instance [IsPattern β α] : Coe (PatternDescr α β) (Pattern α β) := ⟨(.ofDescr ·)⟩

@[inherit_doc PatternDescr.all, inline]
public def Pattern.not [IsPattern β α] (p : Pattern α β) : Pattern α β :=
  PatternDescr.not p

@[inherit_doc PatternDescr.all, inline]
public def Pattern.all [IsPattern β α] (ps : Array (Pattern α β)) : Pattern α β :=
  PatternDescr.all ps

@[inherit_doc PatternDescr.all, inline]
public def Pattern.any [IsPattern β α] (ps : Array (Pattern α β)) : Pattern α β :=
  PatternDescr.any ps

/-- Matches nothing. -/
public def PatternDescr.empty : PatternDescr α β := .any #[]

@[inherit_doc PatternDescr.empty]
public def Pattern.empty : Pattern α β :=
  {filter := fun _ => false, descr? := some .empty, name := `empty}

public instance : EmptyCollection (PatternDescr α β) := ⟨.empty⟩
public instance : EmptyCollection (Pattern α β) := ⟨.empty⟩

/-- Matches everything. -/
public def PatternDescr.star : PatternDescr α β := .all #[]

@[inherit_doc PatternDescr.star]
public def Pattern.star : Pattern α β :=
  {filter := fun _ => true, descr? := some .star, name := `star}

/-! ## String Patterns -/

/-- A declarative `String` pattern. Matches some subset of strings. -/
public inductive StrPatDescr
/-- Matches a string that is a member of the array -/
| mem (xs : Array String)
/-- Matches a string that starts with this prefix. -/
| startsWith (affix : String)
/-- Matches a string that ends with this suffix. -/
| endsWith (affix : String)
deriving Inhabited

/-- Returns whether the string matches the pattern. -/
public def StrPatDescr.matches (s : String) (self : StrPatDescr) : Bool :=
  match self with
  | .mem xs => xs.contains s
  | .startsWith x => s.startsWith x
  | .endsWith x => s.endsWith x

public instance : IsPattern StrPatDescr String := ⟨flip StrPatDescr.matches⟩

/-- A `String` pattern. Matches some subset of strings. -/
public abbrev StrPat := Pattern String StrPatDescr

@[inherit_doc StrPatDescr.mem, inline]
public def StrPat.mem (xs : Array String) : StrPat :=
  StrPatDescr.mem xs

public instance : Coe (Array String) StrPatDescr := ⟨.mem⟩
public instance : Coe (Array String) StrPat := ⟨.mem⟩

@[inherit_doc StrPatDescr.startsWith, inline]
public def StrPat.startsWith (affix : String) : StrPat :=
  StrPatDescr.startsWith affix

@[inherit_doc StrPatDescr.endsWith, inline]
public def StrPat.endsWith (affix : String) : StrPat :=
  StrPatDescr.endsWith affix

/-- Matches a string that is equal to this one. -/
public def StrPatDescr.beq (s : String) : StrPatDescr := .mem #[s]

@[inherit_doc StrPatDescr.beq, inline]
public def StrPat.beq (s : String) : StrPat :=
  {filter := (· == s), descr? := some <| StrPatDescr.beq s, name := `beq}

public instance : Coe String StrPatDescr := ⟨.beq⟩
public instance : Coe String StrPat := ⟨.beq⟩

/-! ## File Path Patterns -/

/-- A declarative `FilePath` pattern. Matches some subset of file paths. -/
public inductive PathPatDescr
/-- Matches a file path whose normalized string representation satisfies the pattern. -/
| path (p : StrPat)
/-- Matches a file path whose extension satisfies the pattern. -/
| extension (p : StrPat)
/-- Matches a file path whose name satisfies the pattern. -/
| fileName (p : StrPat)
deriving Inhabited

/-- Matches a file path that is equal to this one (when both are normalized). -/
@[inline] public def PathPatDescr.eq (p : FilePath) : PathPatDescr :=
  .path p.toString

/-- Returns whether the file path matches the pattern. -/
public def PathPatDescr.matches (path : FilePath) (self : PathPatDescr) : Bool :=
  match self with
  | .path p => p =~ path.normalize.toString
  | .extension p => path.extension.any (p =~ ·)
  | .fileName p => path.fileName.any (p =~ ·)

public instance : IsPattern PathPatDescr FilePath := ⟨flip PathPatDescr.matches⟩

/-- A `FilePath` pattern. Matches some subset of file paths. -/
public abbrev PathPat := Pattern FilePath PathPatDescr

@[inherit_doc PathPatDescr.path, inline]
public def PathPat.path (p : StrPat) : PathPat :=
  PathPatDescr.path p

@[inherit_doc PathPatDescr.extension, inline]
public def PathPat.extension (p : StrPat) : PathPat :=
  PathPatDescr.extension p

@[inherit_doc PathPatDescr.fileName, inline]
public def PathPat.fileName (p : StrPat) : PathPat :=
  PathPatDescr.fileName p

/-! ## Version-specific Patterns -/

/--
Whether a string is "version-like".
That is, a `v` followed by a digit.
-/
public def isVerLike (s : String) : Bool :=
  if h : s.utf8ByteSize ≥ 2 then
    String.Pos.Raw.get' s 0 (by simp [-String.utf8ByteSize_eq_zero_iff, String.Pos.Raw.atEnd]; omega) == 'v' &&
    (String.Pos.Raw.get' s ⟨1⟩ (by simp [String.Pos.Raw.atEnd]; omega)).isDigit
  else
    false

/-- Matches a "version-like" string: a `v` followed by a digit. -/
public def StrPat.verLike : StrPat := .ofFn isVerLike `verLike

/-- Default string pattern for a Package's `versionTags`. -/
public def defaultVersionTags : StrPat := .ofFn isVerLike `default

/-- Builtin `StrPat` presets available to TOML for `versionTags`. -/
public def versionTagPresets :=
  NameMap.empty
  |>.insert `verLike .verLike
  |>.insert `default defaultVersionTags
