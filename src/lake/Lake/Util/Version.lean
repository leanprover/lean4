/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lean.Data.Json
public import Lake.Util.Date
import Init.Data.String.Slice
import Init.Data.String.TakeDrop
import Lean.Data.Trie

/-! # Version

This module contains useful definitions for manipulating versions.
-/

open System Lean

namespace Lake

/-! ## Parser Utils -/

/--
Parses version components separated by a `.` from the head of the string.

Components are composed of alphanumerics or a `*`.
-/
@[inline] def parseVerComponents
  (s : String)
: EStateM String s.ValidPos (Array String.Slice) :=
  fun p => go #[] p p (Nat.le_refl _)
where
  go cs iniPos p (iniPos_le : iniPos.offset.byteIdx ≤ p.offset.byteIdx) :=
    if h : p = s.endValidPos then
      let c := String.Slice.mk s iniPos p iniPos_le
      .ok (cs.push c) p
    else
      let c := p.get h
      if c == '.' then
        let c := String.Slice.mk s iniPos p iniPos_le
        go (cs.push c) (p.next h) (p.next h) (Nat.le_refl _)
      else if c.isAlphanum || c == '*' then
        go cs iniPos (p.next h) <| by
          apply Nat.le_trans iniPos_le
          rw [String.ValidPos.byteIdx_offset_next]
          exact Nat.le_add_right ..
      else
        let c := String.Slice.mk s iniPos p iniPos_le
        .ok (cs.push c) p
  termination_by s.utf8ByteSize - p.offset.byteIdx
  decreasing_by
    all_goals
    rw [p.byteIdx_offset_next]
    have := (p.get h).utf8Size_pos
    have := p.byteIdx_lt_utf8ByteSize h
    omega

/-- Returns whether a version component is a wildcard. -/
private def isWildVer (s : String.Slice) : Bool :=
  let p := s.startPos
  if h : p ≠ s.endPos then
    if p.next h = s.endPos then
      let c := s.startPos.get h
      c == 'x' || c == 'X' || c == '*'
    else false
  else false

@[inline] private def parseVerNat (what : String) (s : String.Slice) : EStateM String σ Nat := do
  let some v := s.toNat?
    | throw s!"invalid {what} version: expected numeral, got '{s.copy}'"
  return v

inductive VerComponent
| none | wild | nat (n : Nat)

private def parseVerComponent {σ} (what : String) (s? : Option String.Slice) : EStateM String σ VerComponent := do
    let some s := s?
      | return .none
    if isWildVer s then
      return .wild
    let some n := s.toNat?
      | throw s!"invalid {what} version: expected numeral or wildcard, got '{s.copy}'"
    return .nat n

def parseSpecialDescr (s : String) : EStateM String s.ValidPos String := do
  let p ← get
  if h : p = s.endValidPos then
    return ""
  else
    let c := p.get h
    if c == '-' then
      let p := p.next h
      let p' := nextUntilWhitespace p
      set p'
      let specialDescr := p.extract p'
      if specialDescr.isEmpty then
        throw "invalid version: '-' suffix cannot be empty"
      return specialDescr
    else
      return ""
where
  nextUntilWhitespace p :=
    if h : p = s.endValidPos then
      p
    else if (p.get h).isWhitespace then
      p
    else
      nextUntilWhitespace (p.next h)
  termination_by s.utf8ByteSize - p.offset.byteIdx
  decreasing_by
    rw [p.byteIdx_offset_next]
    have := (p.get h).utf8Size_pos
    have := p.byteIdx_lt_utf8ByteSize h
    omega


private def runVerParse
  (s : String) (x : (s : String) → EStateM String s.ValidPos α)
  (startPos := s.startValidPos) (endPos := s.endValidPos)
: Except String α :=
  match x s startPos with
  | .ok v p =>
    if p = endPos then
      return v
    else
      let tail := p.offset.extract s endPos.offset
      throw s!"unexpected characters at end of version: {tail}"
  | .error e _ => throw e

/-! ## SemVerCore -/

/-- The major-minor-patch triple of a [SemVer](https://semver.org/). -/
public structure SemVerCore where
  major : Nat := 0
  minor : Nat := 0
  patch : Nat := 0
  deriving Inhabited, Repr, DecidableEq, Ord

namespace SemVerCore

public instance : LT SemVerCore := ltOfOrd
public instance : LE SemVerCore := leOfOrd
public instance : Min SemVerCore := minOfLe
public instance : Max SemVerCore := maxOfLe

def parseM (s : String) : EStateM String s.ValidPos SemVerCore := do
  try
    let cs ← parseVerComponents s
    if h : cs.size = 3 then
      let major ← parseVerNat "major" cs[0]
      let minor ← parseVerNat "minor" cs[1]
      let patch ← parseVerNat "patch" cs[2]
      return {major, minor, patch}
    else
      throw s!"incorrect number of components: got {cs.size}, expected 3"
  catch e =>
    throw s!"invalid version core: {e}"

@[inline] public def parse (s : String) : Except String SemVerCore := do
  runVerParse s parseM

public protected def toString (ver : SemVerCore) : String :=
  s!"{ver.major}.{ver.minor}.{ver.patch}"

public instance : ToString SemVerCore := ⟨SemVerCore.toString⟩
public instance : ToJson SemVerCore := ⟨(·.toString)⟩
public instance : FromJson SemVerCore := ⟨(do SemVerCore.parse <| ← fromJson? ·)⟩

end SemVerCore

/-! ## StdVer -/

/--
A Lean-style semantic version.
A major-minor-patch triple with an optional arbitrary `-` suffix.
-/
public structure StdVer extends SemVerCore where
  specialDescr : String := ""
  deriving Inhabited, Repr, DecidableEq

/-- A Lean version. -/
public abbrev LeanVer := StdVer

namespace StdVer

public instance : Coe StdVer SemVerCore := ⟨StdVer.toSemVerCore⟩

@[inline] public def ofSemVerCore (ver : SemVerCore) : StdVer :=
  {toSemVerCore := ver, specialDescr := ""}

public instance : Coe SemVerCore StdVer := ⟨StdVer.ofSemVerCore⟩

public protected def compare (a b : StdVer) : Ordering :=
  match compare a.toSemVerCore b.toSemVerCore with
  | .eq =>
    match a.specialDescr, b.specialDescr with
    | "", "" => .eq
    |  _, "" => .lt
    | "",  _ => .gt
    | a, b => compare a b
  | ord => ord

public instance : Ord StdVer := ⟨StdVer.compare⟩

public instance : LT StdVer := ltOfOrd
public instance : LE StdVer := leOfOrd
public instance : Min StdVer := minOfLe
public instance : Max StdVer := maxOfLe

public def parseM (s : String) : EStateM String s.ValidPos StdVer := do
  let core ← SemVerCore.parseM s
  let specialDescr ← parseSpecialDescr s
  return {toSemVerCore := core, specialDescr}

@[inline] public def parse (s : String) : Except String StdVer := do
  runVerParse s parseM

public protected def toString (ver : StdVer) : String :=
  if ver.specialDescr.isEmpty then
    ver.toSemVerCore.toString
  else
    s!"{ver.toSemVerCore}-{ver.specialDescr}"

public instance : ToString StdVer := ⟨StdVer.toString⟩
public instance : ToJson StdVer := ⟨(·.toString)⟩
public instance : FromJson StdVer := ⟨(do StdVer.parse <| ← fromJson? ·)⟩

end StdVer

/-! ## ToolchainVer -/

/-- The `elan` toolchain file name (i.e., `lean-toolchain`). -/
public def toolchainFileName : FilePath := "lean-toolchain"

public def ToolchainVer.defaultOrigin := "leanprover/lean4"
public def ToolchainVer.prOrigin := "leanprover/lean4-pr-releases"

public section -- for `@[computed_field]`
open ToolchainVer in
/-- A Lean toolchain version. -/
inductive ToolchainVer
| release (ver : LeanVer)
| nightly (date : Date)
| pr (n : Nat)
| other (v : String)
with
  @[computed_field] toString : ToolchainVer → String
    | .release ver => s!"{defaultOrigin}:v{ver}"
    | .nightly date => s!"{defaultOrigin}:nightly-{date}"
    | .pr n => s!"{prOrigin}:pr-release-{n}"
    | .other v => v
deriving Repr, DecidableEq
end

namespace ToolchainVer

public instance : Coe LeanVer ToolchainVer := ⟨ToolchainVer.release⟩

public def ofString (ver : String) : ToolchainVer := Id.run do
  let colonPos := ver.posOf ':'
  let (origin, tag) :=
    if h : colonPos < ver.rawEndPos then
      let pos := colonPos.next' ver (by simp_all [String.rawEndPos, String.Pos.Raw.atEnd, String.Pos.Raw.lt_iff])
      (String.Pos.Raw.extract ver 0 colonPos, String.Pos.Raw.extract ver pos ver.rawEndPos)
    else
      ("", ver)
  let noOrigin := origin.isEmpty
  if tag.startsWith "v" then
    if let .ok ver := StdVer.parse (tag.drop 1) then
      if noOrigin|| origin == defaultOrigin then
        return .release ver
  else if let some date := tag.dropPrefix? "nightly-" then
    if let some date := Date.ofString? date.toString then
      if noOrigin then
        return .nightly date
      else if let some suffix := origin.dropPrefix? defaultOrigin then
        if suffix.isEmpty || suffix == "-nightly".toSubstring then
          return .nightly date
  else if let some n := tag.dropPrefix?  "pr-release-" then
    if let some n := n.toNat? then
      if noOrigin || origin == prOrigin then
        return .pr n
  else if let .ok ver := StdVer.parse ver then
    if noOrigin || origin == defaultOrigin then
      return .release ver
  return .other ver

/-- Parse a toolchain from a `lean-toolchain` file. -/
public def ofFile? (toolchainFile : FilePath) : IO (Option ToolchainVer) := do
  try
    let toolchainString ← IO.FS.readFile toolchainFile
    return some <| ToolchainVer.ofString toolchainString.trim
  catch
    | .noFileOrDirectory .. =>
      return none
    | e => throw e

/-- Parse a toolchain from the `lean-toolchain` file of the directory `dir`. -/
@[inline] public def ofDir? (dir : FilePath) : IO (Option ToolchainVer) :=
  ToolchainVer.ofFile? (dir / toolchainFileName)

public instance : ToString ToolchainVer := ⟨ToolchainVer.toString⟩
public instance : ToJson ToolchainVer := ⟨(·.toString)⟩
public instance : FromJson ToolchainVer := ⟨(ToolchainVer.ofString <$> fromJson? ·)⟩

public def blt (a b : ToolchainVer) : Bool :=
  match a, b with
  | .release v1, .release v2 => v1 < v2
  | .nightly d1, .nightly d2 => d1 < d2
  | _, _ => false

public instance : LT ToolchainVer := ⟨(·.blt ·)⟩
public instance decLt (a b : ToolchainVer) : Decidable (a < b) :=
  decidable_of_bool (a.blt b) Iff.rfl

public def ble (a b : ToolchainVer) : Bool :=
  match a, b with
  | .release v1, .release v2 => v1 ≤ v2
  | .nightly d1, .nightly d2 => d1 ≤ d2
  | .pr n1, .pr n2 => n1 = n2
  | .other v1, .other v2 => v1 = v2
  | _, _ => false

public instance : LE ToolchainVer := ⟨(·.ble ·)⟩
public instance decLe (a b : ToolchainVer) : Decidable (a ≤ b) :=
  decidable_of_bool (a.ble b) Iff.rfl

end ToolchainVer

/-- Converts a toolchain version to its normal form (e.g., with an origin). -/
public def normalizeToolchain (s : String) : String :=
  ToolchainVer.ofString s |>.toString

/-! ## DecodeVersion -/

/-- Parses a version from a string. -/
public class DecodeVersion (α : Type u) where
  decodeVersion : String → Except String α

export DecodeVersion (decodeVersion)

public instance : DecodeVersion SemVerCore := ⟨SemVerCore.parse⟩
@[default_instance] public instance : DecodeVersion StdVer := ⟨StdVer.parse⟩
public instance : DecodeVersion ToolchainVer := ⟨(pure <| ToolchainVer.ofString ·)⟩

/-! ## VerRange -/

public inductive Comparator
| lt | le | gt | ge | eq | ne
deriving Repr, Inhabited

namespace Comparator

def parseM
  (s : String)
: EStateM String s.ValidPos Comparator := fun p =>
  if let some (tk, op) := trie.matchPrefix s p.offset then
    let p' := p.offset + tk
    if h : p'.isValid s then
      .ok op (.mk p' (String.Pos.Raw.isValid_eq_true_iff.mp h))
    else
      .error "(internal) comparison operator parse produced invalid position" p
  else
    .error "expected comparison operator" p
where trie :=
  let add sym cmp t := t.insert sym (sym, cmp)
  (∅ : Lean.Data.Trie (String × Comparator))
  |> add "<"  .lt
  |> add "<=" .le
  |> add "≤"  .le
  |> add ">"  .gt
  |> add ">=" .ge
  |> add "≥"  .ge
  |> add "="  .eq
  |> add "!=" .ne
  |> add "≠"  .ne

public def ofString? (s : String) : Option Comparator :=
  match parseM s s.startValidPos with
  | .ok op p => if p = s.endValidPos then some op else none
  | .error .. => none

public protected def toString (self : Comparator) : String :=
  match self with
  | .lt => "<"
  | .le => "≤"
  | .gt => ">"
  | .ge => "≥"
  | .eq => "="
  | .ne => "≠"

public instance : ToString Comparator := ⟨Comparator.toString⟩

end Comparator

public structure VerComparator where
  private innerMk ::
    private ver : StdVer
    private op : Comparator
    private includePrereleases : Bool := false
    deriving Repr

namespace VerComparator

/-- A version comparator that matches any non-prerelease version (i.e., `*`, `≥0.0.0`). -/
public def wild : VerComparator :=
  {op := .ge, ver := .ofSemVerCore {}}

public instance : Inhabited VerComparator := ⟨.wild⟩

def parseM (s : String) : EStateM String s.ValidPos VerComparator := do
  let op ← Comparator.parseM s
  let ver ← StdVer.parseM s
  return {ver, op}

@[inline] public def parse (s : String) : Except String VerComparator := do
  runVerParse s parseM

public def test (self : VerComparator) (ver : StdVer) : Bool :=
  let fullCheck op selfVer ver :=
    match op with
    | .lt => ver < selfVer
    | .le => ver ≤ selfVer
    | .gt => ver > selfVer
    | .ge => ver ≥ selfVer
    | .eq => ver = selfVer
    | .ne => ver ≠ selfVer
  let {op, ver := selfVer, includePrereleases} := self
  if includePrereleases then
    fullCheck op selfVer ver
  else
    match selfVer.specialDescr, ver.specialDescr with
    | _, "" =>
      fullCheck op selfVer ver
    | "", _ =>
      false
    | selfDescr, verDescr =>
      if selfVer.toSemVerCore = ver.toSemVerCore then
        match op with
        | .lt => verDescr < selfDescr
        | .le => verDescr ≤ selfDescr
        | .gt => verDescr > selfDescr
        | .ge => verDescr ≥ selfDescr
        | .eq => verDescr = selfDescr
        | .ne => verDescr ≠ selfDescr
      else
        false

public protected def toString (self : VerComparator) : String :=
  s!"{self.op}{self.ver}"

public  instance : ToString VerComparator := ⟨VerComparator.toString⟩

end VerComparator

public structure VerRange where
  private innerMk ::
    toString : String
    clauses : Array (Array VerComparator)
    deriving Repr, Inhabited

namespace VerRange

public instance : ToString VerRange := ⟨VerRange.toString⟩

public def ofClauses (clauses : Array (Array VerComparator)) : VerRange :=
  {toString := fmtOrs clauses, clauses}
where
  fmtOrs ors :=
    if h : ors.size = 0 then
      ""
    else
      ors.foldl (init := fmtAnds ors[0]) (start := 1) fun s ands =>
        s!"{s} || {fmtAnds ands}"
  fmtAnds ands :=
    if h : ands.size = 0 then
      "<empty>"
    else
      ands.foldl (init := ands[0].toString) (start := 1) fun s v =>
        s!"{s}, {v}"

partial def parseM (s : String) : EStateM String s.ValidPos VerRange := do
  let clauses ← go true #[] #[]
  return {toString := s, clauses}
where
  go needsRange ors (ands : Array VerComparator) p :=
    if h : p = s.endValidPos then
      if needsRange || ands.size == 0 then
        .error "expected version range" p
      else
        .ok (ors.push ands) p
    else
      let c := p.get h
      if c.isAlphanum || c == '*' then
        match parseWild s ands p with
        | .ok ands p =>
          go false ors ands p
        | .error e p => .error e p
      else if c == '^' then
        .error "caret ranges are unsupported; \
          if a specific major version is desired, use a tilde or wildcard range; \
          otherwise, use '≥' instead" p
      else if c == '~' then
        match parseTilde s ands (p.next h) with
        | .ok ands p =>
          go false ors ands p
        | .error e p => .error e p
      else if c.isWhitespace then
        go needsRange ors ands (p.next h)
      else if c == ',' then
        if needsRange then
          .error "expected version range" p
        else
          go true ors ands (p.next h)
      else if c == '|' then
        let p := p.next h
        if h : p = s.endValidPos then
          .error "expected '|' after first '|'" p
        else if p.get h = '|' then
          if ands.size = 0 then
            .error "expected version range" p
          else
            go true (ors.push ands) #[] (p.next h)
        else
          .error "expected '|' after first '|'" p
      else
        match VerComparator.parseM s p with
        | .ok cmp p =>
          go false ors (ands.push cmp) p
        | .error e p => .error e p
  @[inline] appendRange ands minVer maxVer (specialDescr := "") :=
    let minVer := StdVer.mk minVer specialDescr
    let maxVer := StdVer.ofSemVerCore maxVer
    ands.push {op := .ge, ver := minVer} |>.push {op := .lt, ver := maxVer, includePrereleases := true}
  parseWild (s : String) ands : EStateM String s.ValidPos _ := do
    let cs ← parseVerComponents s
    if (← get).get?.any (· == '-') then
      throw s!"invalid wildcard range: wildcard versions do not support suffixes"
    else if cs.size = 0 ∨ cs.size > 3 then
      throw s!"invalid wildcard range: incorrect number of components: got {cs.size}, expected 1-3"
    else
      let major? ← parseVerComponent "major" cs[0]?
      let minor? ← parseVerComponent "minor" cs[1]?
      let patch? ← parseVerComponent "patch" cs[2]?
      match major?, minor?, patch? with
      | .nat major, .nat minor, .wild =>
        return appendRange ands {major, minor} {major, minor := minor + 1}
      | .wild, _, .nat _ | _, .wild, .nat _ =>
        throw "invalid patch version: components after a wildcard must be wildcards"
      | .wild, .nat _, _ =>
        throw "invalid minor version: components after a wildcard must be wildcards"
      | .nat major, .wild, _ =>
        return appendRange ands {major} {major := major + 1}
      | .nat _, _, _ =>
        throw "invalid version range: bare versions are not supported; \
          if you want to fix a specific version, use '=' before the full version; \
          otherwise, use '≥' to support it and future versions"
      | _, _, _ =>
        return ands.push .wild
  parseTilde (s : String) ands : EStateM String s.ValidPos _ := do
    let cs ← parseVerComponents s
    let specialDescr ← parseSpecialDescr s
    if h : cs.size = 1 then
      let major ← parseVerNat "major" cs[0]
      return appendRange ands {major} {major := major + 1} specialDescr
    else if h : cs.size = 2 then
      let major ← parseVerNat "major" cs[0]
      let minor ← parseVerNat "minor" cs[1]
      return appendRange ands {major, minor} {major, minor := minor + 1} specialDescr
    else if h : cs.size = 3 then
      let major ← parseVerNat "major" cs[0]
      let minor ← parseVerNat "minor" cs[1]
      let patch ← parseVerNat "patch" cs[2]
      return appendRange ands {major, minor, patch} {major, minor, patch := patch + 1} specialDescr
    else
      throw s!"invalid tilde range: incorrect number of components: got {cs.size}, expected 1-3"

@[inline] public def parse (s : String) : Except String VerRange := do
  runVerParse s parseM

public def test (self : VerRange) (ver : StdVer) : Bool :=
  self.clauses.any (·.all (·.test ver))

end VerRange
