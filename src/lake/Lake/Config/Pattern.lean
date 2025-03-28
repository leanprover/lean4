/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Util.Name

open System Lean

namespace Lake

/-! ## Match Notation -/

class IsPattern (α : Type u) (β : outParam $ Type v) where
  /-- Returns whether the value matches the pattern. -/
  satisfies (pat : α) (val : β) : Bool

@[inherit_doc] scoped infix:50 " =~ " => IsPattern.satisfies

/-! ## Abstract Patterns -/

mutual

/--
A pattern. Matches some subset of the values of a type.
May also include a declarative description.
-/
structure Pattern (α : Type u) (β : Type v) where
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
inductive PatternDescr (α : Type u) (β : Type v)
/-- Matches a value that does not satisfy the pattern. -/
| not (p : Pattern α β)
/-- Matches a value that satisfies every pattern. Short-circuits. -/
| all (ps : Array (Pattern α β))
/-- Matches a value that satisfies any one of the patterns. Short-circuits. -/
| any (ps : Array (Pattern α β))
/-- Matches a value that statisfies the underlying pattern description. -/
| coe (p : β)
deriving Inhabited

end

instance : Coe β (PatternDescr α β) := ⟨.coe⟩

/-- Returns whether the value matches the pattern. Alias for `filter`. -/
abbrev Pattern.matches (a : α) (self : Pattern α β) : Bool :=
  self.filter a

instance : IsPattern (Pattern α β) α := ⟨Pattern.filter⟩

/-- Returns whether the value matches the pattern. -/
@[specialize] def PatternDescr.matches
  [IsPattern β α] (val : α) (self : PatternDescr α β)
: Bool :=
  match self with
  | .not p => !(p =~ val)
  | .all ps => ps.all (· =~ val)
  | .any ps => ps.any (· =~ val)
  | .coe p => p =~ val

instance [IsPattern β α] : IsPattern (PatternDescr α β) α := ⟨flip PatternDescr.matches⟩

/--
Matches a value that satisfies an arbitrary predicate
(optionally identified by a `Name`).
-/
@[inline] def Pattern.ofFn (f : α → Bool) (name := Name.anonymous) : Pattern α β :=
  {filter := f, name}

instance : Coe (α → Bool) (Pattern α β) := ⟨.ofFn⟩

/--
Matches a string that satisfies the declarative pattern.
(optionally identified by a `Name`).
-/
@[inline] def Pattern.ofDescr [IsPattern β α] (descr : PatternDescr α β) (name := Name.anonymous) : Pattern α β :=
  {filter := (descr =~ ·), descr? := descr, name}

instance [IsPattern β α] : Coe (PatternDescr α β) (Pattern α β) := ⟨(.ofDescr ·)⟩

@[inherit_doc PatternDescr.all, inline]
def Pattern.not [IsPattern β α] (p : Pattern α β) : Pattern α β :=
  PatternDescr.not p

@[inherit_doc PatternDescr.all, inline]
def Pattern.all [IsPattern β α] (ps : Array (Pattern α β)) : Pattern α β :=
  PatternDescr.all ps

@[inherit_doc PatternDescr.all, inline]
def Pattern.any [IsPattern β α] (ps : Array (Pattern α β)) : Pattern α β :=
  PatternDescr.any ps

/-- Matches nothing. -/
def PatternDescr.empty : PatternDescr α β := .any #[]

@[inherit_doc PatternDescr.empty]
def Pattern.empty : Pattern α β :=
  {filter := fun _ => false, descr? := some .empty, name := `empty}

instance : EmptyCollection (PatternDescr α β) := ⟨.empty⟩
instance : EmptyCollection (Pattern α β) := ⟨.empty⟩

/-- Matches eveything. -/
def PatternDescr.star : PatternDescr α β := .all #[]

@[inherit_doc PatternDescr.star]
def Pattern.star : Pattern α β :=
  {filter := fun _ => true, descr? := some .star, name := `star}

/-! ## String Patterns -/

/-- A declarative `String` pattern. Matches some subset of strings. -/
inductive StrPatDescr
/-- Matches a string that is a member of the array -/
| mem (xs : Array String)
/-- Matches a string that starts with this prefix. -/
| startsWith (affix : String)
/-- Matches a string that ends with this suffix. -/
| endsWith (affix : String)
deriving Inhabited

/-- Returns whether the string matches the pattern. -/
def StrPatDescr.matches (s : String) (self : StrPatDescr) : Bool :=
  match self with
  | .mem xs => xs.contains s
  | .startsWith x => s.startsWith x
  | .endsWith x => s.endsWith x

instance : IsPattern StrPatDescr String := ⟨flip StrPatDescr.matches⟩

/-- A `String` pattern. Matches some subset of strings. -/
abbrev StrPat := Pattern String StrPatDescr

@[inherit_doc Pattern.empty, deprecated Pattern.empty (since := "2025-03-27")]
abbrev StrPat.none : StrPat := Pattern.empty

@[inherit_doc Pattern.ofFn, deprecated Pattern.ofFn (since := "2025-03-27")]
abbrev StrPat.satisfies (f : String → Bool) (name := Name.anonymous) : StrPat :=
  Pattern.ofFn f name

@[inherit_doc StrPatDescr.mem, inline]
def StrPat.mem (xs : Array String) : StrPat :=
  StrPatDescr.mem xs

instance : Coe (Array String) StrPatDescr := ⟨.mem⟩
instance : Coe (Array String) StrPat := ⟨.mem⟩

@[inherit_doc StrPatDescr.startsWith, inline]
def StrPat.startsWith (affix : String) : StrPat :=
  StrPatDescr.startsWith affix

@[inherit_doc StrPatDescr.endsWith, inline]
def StrPat.endsWith (affix : String) : StrPat :=
  StrPatDescr.endsWith affix

/-- Matches a string that is equal to this one. -/
def StrPatDescr.beq (s : String) : StrPatDescr := .mem #[s]

@[inherit_doc StrPatDescr.mem, inline]
def StrPat.beq (s : String) : StrPat :=
  {filter := (· == s), descr? := some <| StrPatDescr.beq s}

instance : Coe String StrPatDescr := ⟨.beq⟩
instance : Coe String StrPat := ⟨.beq⟩

/-! ## File Path Patterns -/

/-- A declarative `FilePath` pattern. Matches some subset of file paths. -/
inductive PathPatDescr
/-- Matches a file path whose normalized string representation satisfies the pattern. -/
| path (p : StrPat)
/-- Matches a file path whose extension satisfies the pattern. -/
| extension (p : StrPat)
/-- Matches a file path whose name satisfies the pattern. -/
| fileName (p : StrPat)
deriving Inhabited

/-- Matches a file path that is equal to this one (when both are normalized). -/
@[inline] def PathPatDescr.eq (p : FilePath) : PathPatDescr :=
  .path p.toString

/-- Returns whether the string matches the pattern. -/
def PathPatDescr.matches (path : FilePath) (self : PathPatDescr) : Bool :=
  match self with
  | .path p => p =~ path.normalize.toString
  | .extension p => path.extension.any (p =~ ·)
  | .fileName p => path.fileName.any (p =~ ·)

instance : IsPattern PathPatDescr FilePath := ⟨flip PathPatDescr.matches⟩

/-- A `FilePath` pattern. Matches some subset of file paths. -/
abbrev PathPat := Pattern FilePath PathPatDescr

@[inherit_doc PathPatDescr.path, inline]
def PathPat.path (p : StrPat) : PathPat :=
  PathPatDescr.path p

@[inherit_doc PathPatDescr.extension, inline]
def PathPat.extension (p : StrPat) : PathPat :=
  PathPatDescr.extension p

@[inherit_doc PathPatDescr.fileName, inline]
def PathPat.fileName (p : StrPat) : PathPat :=
  PathPatDescr.fileName p

/-! ## Version-specific Patterns -/

/--
Whether a string is "version-like".
That is, a `v` followed by a digit.
-/
def isVerLike (s : String) : Bool :=
  if h : s.utf8ByteSize ≥ 2 then
    s.get' 0 (by simp [String.atEnd]; omega) == 'v' &&
    (s.get' ⟨1⟩ (by simp [String.atEnd]; omega)).isDigit
  else
    false

/-- Matches a "version-like" string: a `v` followed by a digit. -/
def StrPat.verLike : StrPat := .ofFn isVerLike `verLike

/-- Default string pattern for a Package's `versionTags`. -/
def defaultVersionTags : StrPat := .ofFn isVerLike `default

/-- Builtin `StrPat` presets available to TOML for `versionTags`. -/
def versionTagPresets :=
  NameMap.empty
  |>.insert `verLike .verLike
  |>.insert `default defaultVersionTags
