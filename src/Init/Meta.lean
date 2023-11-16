/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura and Sebastian Ullrich

Additional goodies for writing macros
-/
prelude
import Init.MetaTypes
import Init.Data.Array.Basic
import Init.Data.Option.BasicAux

namespace Lean

@[extern "lean_version_get_major"]
private opaque version.getMajor (u : Unit) : Nat
def version.major : Nat := version.getMajor ()

@[extern "lean_version_get_minor"]
private opaque version.getMinor (u : Unit) : Nat
def version.minor : Nat := version.getMinor ()

@[extern "lean_version_get_patch"]
private opaque version.getPatch (u : Unit) : Nat
def version.patch : Nat := version.getPatch ()

@[extern "lean_get_githash"]
opaque getGithash (u : Unit) : String
def githash : String := getGithash ()

@[extern "lean_version_get_is_release"]
opaque version.getIsRelease (u : Unit) : Bool
def version.isRelease : Bool := version.getIsRelease ()

/-- Additional version description like "nightly-2018-03-11" -/
@[extern "lean_version_get_special_desc"]
opaque version.getSpecialDesc (u : Unit) : String
def version.specialDesc : String := version.getSpecialDesc ()

def versionStringCore :=
  toString version.major ++ "." ++ toString version.minor ++ "." ++ toString version.patch

def versionString :=
  if version.specialDesc ≠ "" then
    versionStringCore ++ "-" ++ version.specialDesc
  else if version.isRelease then
    versionStringCore
  else
    versionStringCore ++ ", commit " ++ githash

def origin :=
  "leanprover/lean4"

def toolchain :=
  if version.specialDesc ≠ ""  then
    if version.isRelease then
      origin ++ ":" ++ versionStringCore ++ "-" ++ version.specialDesc
    else
      origin ++ ":" ++ version.specialDesc
  else if version.isRelease then
    origin ++ ":" ++ versionStringCore
  else
    ""

@[extern "lean_internal_is_stage0"]
opaque Internal.isStage0 (u : Unit) : Bool

/--
This function can be used to detect whether the compiler has support for
generating LLVM instead of C. It is used by lake instead of the --features
flag in order to avoid having to run a compiler for this every time on startup.
See #2572.
-/
@[extern "lean_internal_has_llvm_backend"]
opaque Internal.hasLLVMBackend (u : Unit) : Bool

/-- Valid identifier names -/
def isGreek (c : Char) : Bool :=
  0x391 ≤ c.val && c.val ≤ 0x3dd

def isLetterLike (c : Char) : Bool :=
  (0x3b1  ≤ c.val && c.val ≤ 0x3c9 && c.val ≠ 0x3bb) ||                  -- Lower greek, but lambda
  (0x391  ≤ c.val && c.val ≤ 0x3A9 && c.val ≠ 0x3A0 && c.val ≠ 0x3A3) || -- Upper greek, but Pi and Sigma
  (0x3ca  ≤ c.val && c.val ≤ 0x3fb) ||                                   -- Coptic letters
  (0x1f00 ≤ c.val && c.val ≤ 0x1ffe) ||                                  -- Polytonic Greek Extended Character Set
  (0x2100 ≤ c.val && c.val ≤ 0x214f) ||                                  -- Letter like block
  (0x1d49c ≤ c.val && c.val ≤ 0x1d59f)                                   -- Latin letters, Script, Double-struck, Fractur

def isNumericSubscript (c : Char) : Bool :=
  0x2080 ≤ c.val && c.val ≤ 0x2089

def isSubScriptAlnum (c : Char) : Bool :=
  isNumericSubscript c ||
  (0x2090 ≤ c.val && c.val ≤ 0x209c) ||
  (0x1d62 ≤ c.val && c.val ≤ 0x1d6a)

def isIdFirst (c : Char) : Bool :=
  c.isAlpha || c = '_' || isLetterLike c

def isIdRest (c : Char) : Bool :=
  c.isAlphanum || c = '_' || c = '\'' || c == '!' || c == '?' || isLetterLike c || isSubScriptAlnum c

def idBeginEscape := '«'
def idEndEscape   := '»'
def isIdBeginEscape (c : Char) : Bool := c = idBeginEscape
def isIdEndEscape (c : Char) : Bool := c = idEndEscape

namespace Name

def getRoot : Name → Name
  | anonymous             => anonymous
  | n@(str anonymous _) => n
  | n@(num anonymous _) => n
  | str n _             => getRoot n
  | num n _             => getRoot n

@[export lean_is_inaccessible_user_name]
def isInaccessibleUserName : Name → Bool
  | Name.str _ s   => s.contains '✝' || s == "_inaccessible"
  | Name.num p _   => isInaccessibleUserName p
  | _              => false

def escapePart (s : String) : Option String :=
  if s.length > 0 && isIdFirst (s.get 0) && (s.toSubstring.drop 1).all isIdRest then s
  else if s.any isIdEndEscape then none
  else some <| idBeginEscape.toString ++ s ++ idEndEscape.toString

-- NOTE: does not roundtrip even with `escape = true` if name is anonymous or contains numeric part or `idEndEscape`
variable (sep : String) (escape : Bool)
def toStringWithSep : Name → String
  | anonymous       => "[anonymous]"
  | str anonymous s => maybeEscape s
  | num anonymous v => toString v
  | str n s         => toStringWithSep n ++ sep ++ maybeEscape s
  | num n v         => toStringWithSep n ++ sep ++ Nat.repr v
where
  maybeEscape s := if escape then escapePart s |>.getD s else s

protected def toString (n : Name) (escape := true) : String :=
  -- never escape "prettified" inaccessible names or macro scopes or pseudo-syntax introduced by the delaborator
  toStringWithSep "." (escape && !n.isInaccessibleUserName && !n.hasMacroScopes && !maybePseudoSyntax) n
where
  maybePseudoSyntax :=
    if let .str _ s := n.getRoot then
      -- could be pseudo-syntax for loose bvar or universe mvar, output as is
      "#".isPrefixOf s || "?".isPrefixOf s
    else
      false

instance : ToString Name where
  toString n := n.toString

private def hasNum : Name → Bool
  | anonymous => false
  | num ..    => true
  | str p ..  => hasNum p

protected def reprPrec (n : Name) (prec : Nat) : Std.Format :=
  match n with
  | anonymous => Std.Format.text "Lean.Name.anonymous"
  | num p i => Repr.addAppParen ("Lean.Name.mkNum " ++ Name.reprPrec p max_prec ++ " " ++ repr i) prec
  | str p s =>
    if p.hasNum then
      Repr.addAppParen ("Lean.Name.mkStr " ++ Name.reprPrec p max_prec ++ " " ++ repr s) prec
    else
      Std.Format.text "`" ++ n.toString

instance : Repr Name where
  reprPrec := Name.reprPrec

def capitalize : Name → Name
  | .str p s => .str p s.capitalize
  | n        => n

def replacePrefix : Name → Name → Name → Name
  | anonymous,   anonymous, newP => newP
  | anonymous,   _,         _    => anonymous
  | n@(str p s), queryP,    newP => if n == queryP then newP else Name.mkStr (p.replacePrefix queryP newP) s
  | n@(num p s), queryP,    newP => if n == queryP then newP else Name.mkNum (p.replacePrefix queryP newP) s

/--
  `eraseSuffix? n s` return `n'` if `n` is of the form `n == n' ++ s`.
-/
def eraseSuffix? : Name → Name → Option Name
  | n,       anonymous => some n
  | str p s, str p' s' => if s == s' then eraseSuffix? p p' else none
  | num p s, num p' s' => if s == s' then eraseSuffix? p p' else none
  | _,       _         => none

/-- Remove macros scopes, apply `f`, and put them back -/
@[inline] def modifyBase (n : Name) (f : Name → Name) : Name :=
  if n.hasMacroScopes then
    let view := extractMacroScopes n
    { view with name := f view.name }.review
  else
    f n

@[export lean_name_append_after]
def appendAfter (n : Name) (suffix : String) : Name :=
  n.modifyBase fun
    | str p s => Name.mkStr p (s ++ suffix)
    | n       => Name.mkStr n suffix

@[export lean_name_append_index_after]
def appendIndexAfter (n : Name) (idx : Nat) : Name :=
  n.modifyBase fun
    | str p s => Name.mkStr p (s ++ "_" ++ toString idx)
    | n       => Name.mkStr n ("_" ++ toString idx)

@[export lean_name_append_before]
def appendBefore (n : Name) (pre : String) : Name :=
  n.modifyBase fun
    | anonymous => Name.mkStr anonymous pre
    | str p s => Name.mkStr p (pre ++ s)
    | num p n => Name.mkNum (Name.mkStr p pre) n

protected theorem beq_iff_eq {m n : Name} : m == n ↔ m = n := by
  show m.beq n ↔ _
  induction m generalizing n <;> cases n <;> simp_all [Name.beq, And.comm]

instance : LawfulBEq Name where
  eq_of_beq := Name.beq_iff_eq.1
  rfl := Name.beq_iff_eq.2 rfl

instance : DecidableEq Name :=
  fun a b => if h : a == b then .isTrue (by simp_all) else .isFalse (by simp_all)

end Name

namespace NameGenerator

@[inline] def curr (g : NameGenerator) : Name :=
  Name.mkNum g.namePrefix g.idx

@[inline] def next (g : NameGenerator) : NameGenerator :=
  { g with idx := g.idx + 1 }

@[inline] def mkChild (g : NameGenerator) : NameGenerator × NameGenerator :=
  ({ namePrefix := Name.mkNum g.namePrefix g.idx, idx := 1 },
   { g with idx := g.idx + 1 })

end NameGenerator

class MonadNameGenerator (m : Type → Type) where
  getNGen : m NameGenerator
  setNGen : NameGenerator → m Unit

export MonadNameGenerator (getNGen setNGen)

def mkFreshId {m : Type → Type} [Monad m] [MonadNameGenerator m] : m Name := do
  let ngen ← getNGen
  let r := ngen.curr
  setNGen ngen.next
  pure r

instance monadNameGeneratorLift (m n : Type → Type) [MonadLift m n] [MonadNameGenerator m] : MonadNameGenerator n := {
  getNGen := liftM (getNGen : m _),
  setNGen := fun ngen => liftM (setNGen ngen : m _)
}

namespace Syntax

deriving instance Repr for Syntax.Preresolved
deriving instance Repr for Syntax
deriving instance Repr for TSyntax

abbrev Term := TSyntax `term
abbrev Command := TSyntax `command
protected abbrev Level := TSyntax `level
protected abbrev Tactic := TSyntax `tactic
abbrev Prec := TSyntax `prec
abbrev Prio := TSyntax `prio
abbrev Ident := TSyntax identKind
abbrev StrLit := TSyntax strLitKind
abbrev CharLit := TSyntax charLitKind
abbrev NameLit := TSyntax nameLitKind
abbrev ScientificLit := TSyntax scientificLitKind
abbrev NumLit := TSyntax numLitKind
abbrev HygieneInfo := TSyntax hygieneInfoKind

end Syntax

export Syntax (Term Command Prec Prio Ident StrLit CharLit NameLit ScientificLit NumLit HygieneInfo)

namespace TSyntax

instance : Coe (TSyntax [k]) (TSyntax (k :: ks)) where
  coe stx := ⟨stx⟩

instance : Coe (TSyntax ks) (TSyntax (k' :: ks)) where
  coe stx := ⟨stx⟩

instance : Coe Ident Term where
  coe s := ⟨s.raw⟩

instance : CoeDep Term ⟨Syntax.ident info ss n res⟩ Ident where
  coe := ⟨Syntax.ident info ss n res⟩

instance : Coe StrLit Term where
  coe s := ⟨s.raw⟩

instance : Coe NameLit Term where
  coe s := ⟨s.raw⟩

instance : Coe ScientificLit Term where
  coe s := ⟨s.raw⟩

instance : Coe NumLit Term where
  coe s := ⟨s.raw⟩

instance : Coe CharLit Term where
  coe s := ⟨s.raw⟩

instance : Coe Ident Syntax.Level where
  coe s := ⟨s.raw⟩

instance : Coe NumLit Prio where
  coe s := ⟨s.raw⟩

instance : Coe NumLit Prec where
  coe s := ⟨s.raw⟩

namespace Compat

scoped instance : CoeTail Syntax (TSyntax k) where
  coe s := ⟨s⟩

scoped instance : CoeTail (Array Syntax) (TSyntaxArray k) where
  coe := .mk

end Compat

end TSyntax

namespace Syntax

deriving instance BEq for Syntax.Preresolved

/-- Compare syntax structures modulo source info. -/
partial def structEq : Syntax → Syntax → Bool
  | Syntax.missing, Syntax.missing => true
  | Syntax.node _ k args, Syntax.node _ k' args' => k == k' && args.isEqv args' structEq
  | Syntax.atom _ val, Syntax.atom _ val' => val == val'
  | Syntax.ident _ rawVal val preresolved, Syntax.ident _ rawVal' val' preresolved' => rawVal == rawVal' && val == val' && preresolved == preresolved'
  | _, _ => false

instance : BEq Lean.Syntax := ⟨structEq⟩
instance : BEq (Lean.TSyntax k) := ⟨(·.raw == ·.raw)⟩

partial def getTailInfo? : Syntax → Option SourceInfo
  | atom info _   => info
  | ident info .. => info
  | node SourceInfo.none _ args =>
      args.findSomeRev? getTailInfo?
  | node info _ _    => info
  | _             => none

def getTailInfo (stx : Syntax) : SourceInfo :=
  stx.getTailInfo?.getD SourceInfo.none

def getTrailingSize (stx : Syntax) : Nat :=
  match stx.getTailInfo? with
  | some (SourceInfo.original (trailing := trailing) ..) => trailing.bsize
  | _ => 0

/--
  Return substring of original input covering `stx`.
  Result is meaningful only if all involved `SourceInfo.original`s refer to the same string (as is the case after parsing). -/
def getSubstring? (stx : Syntax) (withLeading := true) (withTrailing := true) : Option Substring :=
  match stx.getHeadInfo, stx.getTailInfo with
  | SourceInfo.original lead startPos _ _, SourceInfo.original _ _ trail stopPos =>
    some {
      str      := lead.str
      startPos := if withLeading then lead.startPos else startPos
      stopPos  := if withTrailing then trail.stopPos else stopPos
    }
  | _, _ => none

@[specialize] private partial def updateLast {α} [Inhabited α] (a : Array α) (f : α → Option α) (i : Nat) : Option (Array α) :=
  if i == 0 then
    none
  else
    let i := i - 1
    let v := a[i]!
    match f v with
    | some v => some <| a.set! i v
    | none   => updateLast a f i

partial def setTailInfoAux (info : SourceInfo) : Syntax → Option Syntax
  | atom _ val             => some <| atom info val
  | ident _ rawVal val pre => some <| ident info rawVal val pre
  | node info k args       =>
    match updateLast args (setTailInfoAux info) args.size with
    | some args => some <| node info k args
    | none      => none
  | _                      => none

def setTailInfo (stx : Syntax) (info : SourceInfo) : Syntax :=
  match setTailInfoAux info stx with
  | some stx => stx
  | none     => stx

def unsetTrailing (stx : Syntax) : Syntax :=
  match stx.getTailInfo with
  | SourceInfo.original lead pos _ endPos => stx.setTailInfo (SourceInfo.original lead pos "".toSubstring endPos)
  | _                                     => stx

@[specialize] private partial def updateFirst {α} [Inhabited α] (a : Array α) (f : α → Option α) (i : Nat) : Option (Array α) :=
  if h : i < a.size then
    let v := a[i]
    match f v with
    | some v => some <| a.set ⟨i, h⟩ v
    | none   => updateFirst a f (i+1)
  else
    none

partial def setHeadInfoAux (info : SourceInfo) : Syntax → Option Syntax
  | atom _ val             => some <| atom info val
  | ident _ rawVal val pre => some <| ident info rawVal val pre
  | node i k args          =>
    match updateFirst args (setHeadInfoAux info) 0 with
    | some args => some <| node i k args
    | _         => none
  | _                      => none

def setHeadInfo (stx : Syntax) (info : SourceInfo) : Syntax :=
  match setHeadInfoAux info stx with
  | some stx => stx
  | none     => stx

def setInfo (info : SourceInfo) : Syntax → Syntax
  | atom _ val             => atom info val
  | ident _ rawVal val pre => ident info rawVal val pre
  | node _ kind args       => node info kind args
  | missing                => missing

/-- Return the first atom/identifier that has position information -/
partial def getHead? : Syntax → Option Syntax
  | stx@(atom info ..)  => info.getPos?.map fun _ => stx
  | stx@(ident info ..) => info.getPos?.map fun _ => stx
  | node SourceInfo.none _ args => args.findSome? getHead?
  | stx@(node ..) => stx
  | _ => none

def copyHeadTailInfoFrom (target source : Syntax) : Syntax :=
  target.setHeadInfo source.getHeadInfo |>.setTailInfo source.getTailInfo

/-- Ensure head position is synthetic. The server regards syntax as "original" only if both head and tail info are `original`. -/
def mkSynthetic (stx : Syntax) : Syntax :=
  stx.setHeadInfo (SourceInfo.fromRef stx)

end Syntax

/-- Use the head atom/identifier of the current `ref` as the `ref` -/
@[inline] def withHeadRefOnly {m : Type → Type} [Monad m] [MonadRef m] {α} (x : m α) : m α := do
  match (← getRef).getHead? with
  | none => x
  | some ref => withRef ref x

/--
  Expand macros in the given syntax.
  A node with kind `k` is visited only if `p k` is true.

  Note that the default value for `p` returns false for `by ...` nodes.
  This is a "hack". The tactic framework abuses the macro system to implement extensible tactics.
  For example, one can define
  ```lean
  syntax "my_trivial" : tactic -- extensible tactic

  macro_rules | `(tactic| my_trivial) => `(tactic| decide)
  macro_rules | `(tactic| my_trivial) => `(tactic| assumption)
  ```
  When the tactic evaluator finds the tactic `my_trivial`, it tries to evaluate the `macro_rule` expansions
  until one "works", i.e., the macro expansion is evaluated without producing an exception.
  We say this solution is a bit hackish because the term elaborator may invoke `expandMacros` with `(p := fun _ => true)`,
  and expand the tactic macros as just macros. In the example above, `my_trivial` would be replaced with `assumption`,
  `decide` would not be tried if `assumption` fails at tactic evaluation time.

  We are considering two possible solutions for this issue:
  1- A proper extensible tactic feature that does not rely on the macro system.

  2- Typed macros that know the syntax categories they're working in. Then, we would be able to select which
     syntactic categories are expanded by `expandMacros`.
-/
partial def expandMacros (stx : Syntax) (p : SyntaxNodeKind → Bool := fun k => k != `Lean.Parser.Term.byTactic) : MacroM Syntax :=
  withRef stx do
    match stx with
    | .node info k args => do
      if p k then
        match (← expandMacro? stx) with
        | some stxNew => expandMacros stxNew
        | none        => do
          let args ← Macro.withIncRecDepth stx <| args.mapM expandMacros
          return .node info k args
      else
        return stx
    | stx => return stx

/-! # Helper functions for processing Syntax programmatically -/

/--
  Create an identifier copying the position from `src`.
  To refer to a specific constant, use `mkCIdentFrom` instead. -/
def mkIdentFrom (src : Syntax) (val : Name) (canonical := false) : Ident :=
  ⟨Syntax.ident (SourceInfo.fromRef src canonical) (toString val).toSubstring val []⟩

def mkIdentFromRef [Monad m] [MonadRef m] (val : Name) (canonical := false) : m Ident := do
  return mkIdentFrom (← getRef) val canonical

/--
  Create an identifier referring to a constant `c` copying the position from `src`.
  This variant of `mkIdentFrom` makes sure that the identifier cannot accidentally
  be captured. -/
def mkCIdentFrom (src : Syntax) (c : Name) (canonical := false) : Ident :=
  -- Remark: We use the reserved macro scope to make sure there are no accidental collision with our frontend
  let id   := addMacroScope `_internal c reservedMacroScope
  ⟨Syntax.ident (SourceInfo.fromRef src canonical) (toString id).toSubstring id [.decl c []]⟩

def mkCIdentFromRef [Monad m] [MonadRef m] (c : Name) (canonical := false) : m Syntax := do
  return mkCIdentFrom (← getRef) c canonical

def mkCIdent (c : Name) : Ident :=
  mkCIdentFrom Syntax.missing c

@[export lean_mk_syntax_ident]
def mkIdent (val : Name) : Ident :=
  ⟨Syntax.ident SourceInfo.none (toString val).toSubstring val []⟩

@[inline] def mkGroupNode (args : Array Syntax := #[]) : Syntax :=
  mkNode groupKind args

def mkSepArray (as : Array Syntax) (sep : Syntax) : Array Syntax := Id.run do
  let mut i := 0
  let mut r := #[]
  for a in as do
    if i > 0 then
      r := r.push sep |>.push a
    else
      r := r.push a
    i := i + 1
  return r

def mkOptionalNode (arg : Option Syntax) : Syntax :=
  match arg with
  | some arg => mkNullNode #[arg]
  | none     => mkNullNode #[]

def mkHole (ref : Syntax) (canonical := false) : Syntax :=
  mkNode `Lean.Parser.Term.hole #[mkAtomFrom ref "_" canonical]

namespace Syntax

def mkSep (a : Array Syntax) (sep : Syntax) : Syntax :=
  mkNullNode <| mkSepArray a sep

def SepArray.ofElems {sep} (elems : Array Syntax) : SepArray sep :=
⟨mkSepArray elems (if sep.isEmpty then mkNullNode else mkAtom sep)⟩

def SepArray.ofElemsUsingRef [Monad m] [MonadRef m] {sep} (elems : Array Syntax) : m (SepArray sep) := do
  let ref ← getRef;
  return ⟨mkSepArray elems (if sep.isEmpty then mkNullNode else mkAtomFrom ref sep)⟩

instance : Coe (Array Syntax) (SepArray sep) where
  coe := SepArray.ofElems

instance : Coe (TSyntaxArray k) (TSepArray k sep) where
  coe a := ⟨mkSepArray a.raw (mkAtom sep)⟩

/-- Create syntax representing a Lean term application, but avoid degenerate empty applications. -/
def mkApp (fn : Term) : (args : TSyntaxArray `term) → Term
  | #[]  => fn
  | args => ⟨mkNode `Lean.Parser.Term.app #[fn, mkNullNode args.raw]⟩

def mkCApp (fn : Name) (args : TSyntaxArray `term) : Term :=
  mkApp (mkCIdent fn) args

def mkLit (kind : SyntaxNodeKind) (val : String) (info := SourceInfo.none) : TSyntax kind :=
  let atom : Syntax := Syntax.atom info val
  mkNode kind #[atom]

def mkStrLit (val : String) (info := SourceInfo.none) : StrLit :=
  mkLit strLitKind (String.quote val) info

def mkNumLit (val : String) (info := SourceInfo.none) : NumLit :=
  mkLit numLitKind val info

def mkScientificLit (val : String) (info := SourceInfo.none) : TSyntax scientificLitKind :=
  mkLit scientificLitKind val info

def mkNameLit (val : String) (info := SourceInfo.none) : NameLit :=
  mkLit nameLitKind val info

/-! Recall that we don't have special Syntax constructors for storing numeric and string atoms.
   The idea is to have an extensible approach where embedded DSLs may have new kind of atoms and/or
   different ways of representing them. So, our atoms contain just the parsed string.
   The main Lean parser uses the kind `numLitKind` for storing natural numbers that can be encoded
   in binary, octal, decimal and hexadecimal format. `isNatLit` implements a "decoder"
   for Syntax objects representing these numerals. -/

private partial def decodeBinLitAux (s : String) (i : String.Pos) (val : Nat) : Option Nat :=
  if s.atEnd i then some val
  else
    let c := s.get i
    if c == '0' then decodeBinLitAux s (s.next i) (2*val)
    else if c == '1' then decodeBinLitAux s (s.next i) (2*val + 1)
    else none

private partial def decodeOctalLitAux (s : String) (i : String.Pos) (val : Nat) : Option Nat :=
  if s.atEnd i then some val
  else
    let c := s.get i
    if '0' ≤ c && c ≤ '7' then decodeOctalLitAux s (s.next i) (8*val + c.toNat - '0'.toNat)
    else none

private def decodeHexDigit (s : String) (i : String.Pos) : Option (Nat × String.Pos) :=
  let c := s.get i
  let i := s.next i
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat, i)
  else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat, i)
  else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat, i)
  else none

private partial def decodeHexLitAux (s : String) (i : String.Pos) (val : Nat) : Option Nat :=
  if s.atEnd i then some val
  else match decodeHexDigit s i with
    | some (d, i) => decodeHexLitAux s i (16*val + d)
    | none        => none

private partial def decodeDecimalLitAux (s : String) (i : String.Pos) (val : Nat) : Option Nat :=
  if s.atEnd i then some val
  else
    let c := s.get i
    if '0' ≤ c && c ≤ '9' then decodeDecimalLitAux s (s.next i) (10*val + c.toNat - '0'.toNat)
    else none

def decodeNatLitVal? (s : String) : Option Nat :=
  let len := s.length
  if len == 0 then none
  else
    let c := s.get 0
    if c == '0' then
      if len == 1 then some 0
      else
        let c := s.get ⟨1⟩
        if c == 'x' || c == 'X' then decodeHexLitAux s ⟨2⟩ 0
        else if c == 'b' || c == 'B' then decodeBinLitAux s ⟨2⟩ 0
        else if c == 'o' || c == 'O' then decodeOctalLitAux s ⟨2⟩ 0
        else if c.isDigit then decodeDecimalLitAux s 0 0
        else none
    else if c.isDigit then decodeDecimalLitAux s 0 0
    else none

def isLit? (litKind : SyntaxNodeKind) (stx : Syntax) : Option String :=
  match stx with
  | Syntax.node _ k args =>
    if k == litKind && args.size == 1 then
      match args.get! 0 with
      | (Syntax.atom _ val) => some val
      | _ => none
    else
      none
  | _ => none

private def isNatLitAux (litKind : SyntaxNodeKind) (stx : Syntax) : Option Nat :=
  match isLit? litKind stx with
  | some val => decodeNatLitVal? val
  | _        => none

def isNatLit? (s : Syntax) : Option Nat :=
  isNatLitAux numLitKind s

def isFieldIdx? (s : Syntax) : Option Nat :=
  isNatLitAux fieldIdxKind s

/-- Decodes a 'scientific number' string which is consumed by the `OfScientific` class.
  Takes as input a string such as `123`, `123.456e7` and returns a triple `(n, sign, e)` with value given by
  `n * 10^-e` if `sign` else `n * 10^e`.
-/
partial def decodeScientificLitVal? (s : String) : Option (Nat × Bool × Nat) :=
  let len := s.length
  if len == 0 then none
  else
    let c := s.get 0
    if c.isDigit then
      decode 0 0
    else none
where
  decodeAfterExp (i : String.Pos) (val : Nat) (e : Nat) (sign : Bool) (exp : Nat) : Option (Nat × Bool × Nat) :=
    if s.atEnd i then
      if sign then
        some (val, sign, exp + e)
      else if exp >= e then
        some (val, sign, exp - e)
      else
        some (val, true, e - exp)
    else
      let c := s.get i
      if '0' ≤ c && c ≤ '9' then
        decodeAfterExp (s.next i) val e sign (10*exp + c.toNat - '0'.toNat)
      else
        none

  decodeExp (i : String.Pos) (val : Nat) (e : Nat) : Option (Nat × Bool × Nat) :=
    if s.atEnd i then none else
    let c := s.get i
    if c == '-' then
       decodeAfterExp (s.next i) val e true 0
    else if c == '+' then
       decodeAfterExp (s.next i) val e false 0
    else
       decodeAfterExp i val e false 0

  decodeAfterDot (i : String.Pos) (val : Nat) (e : Nat) : Option (Nat × Bool × Nat) :=
    if s.atEnd i then
      some (val, true, e)
    else
      let c := s.get i
      if '0' ≤ c && c ≤ '9' then
        decodeAfterDot (s.next i) (10*val + c.toNat - '0'.toNat) (e+1)
      else if c == 'e' || c == 'E' then
        decodeExp (s.next i) val e
      else
        none

  decode (i : String.Pos) (val : Nat) : Option (Nat × Bool × Nat) :=
    if s.atEnd i then
      none
    else
      let c := s.get i
      if '0' ≤ c && c ≤ '9' then
        decode (s.next i) (10*val + c.toNat - '0'.toNat)
      else if c == '.' then
        decodeAfterDot (s.next i) val 0
      else if c == 'e' || c == 'E' then
        decodeExp (s.next i) val 0
      else
        none

def isScientificLit? (stx : Syntax) : Option (Nat × Bool × Nat) :=
  match isLit? scientificLitKind stx with
  | some val => decodeScientificLitVal? val
  | _        => none

def isIdOrAtom? : Syntax → Option String
  | Syntax.atom _ val           => some val
  | Syntax.ident _ rawVal _ _   => some rawVal.toString
  | _ => none

def toNat (stx : Syntax) : Nat :=
  match stx.isNatLit? with
  | some val => val
  | none     => 0

def decodeQuotedChar (s : String) (i : String.Pos) : Option (Char × String.Pos) := do
  let c := s.get i
  let i := s.next i
  if c == '\\' then pure ('\\', i)
  else if c = '\"' then pure ('\"', i)
  else if c = '\'' then pure ('\'', i)
  else if c = 'r'  then pure ('\r', i)
  else if c = 'n'  then pure ('\n', i)
  else if c = 't'  then pure ('\t', i)
  else if c = 'x'  then
    let (d₁, i) ← decodeHexDigit s i
    let (d₂, i) ← decodeHexDigit s i
    pure (Char.ofNat (16*d₁ + d₂), i)
  else if c = 'u'  then do
    let (d₁, i) ← decodeHexDigit s i
    let (d₂, i) ← decodeHexDigit s i
    let (d₃, i) ← decodeHexDigit s i
    let (d₄, i) ← decodeHexDigit s i
    pure (Char.ofNat (16*(16*(16*d₁ + d₂) + d₃) + d₄), i)
  else
    none

partial def decodeStrLitAux (s : String) (i : String.Pos) (acc : String) : Option String := do
  let c := s.get i
  let i := s.next i
  if c == '\"' then
    pure acc
  else if s.atEnd i then
    none
  else if c == '\\' then do
    let (c, i) ← decodeQuotedChar s i
    decodeStrLitAux s i (acc.push c)
  else
    decodeStrLitAux s i (acc.push c)

def decodeStrLit (s : String) : Option String :=
  decodeStrLitAux s ⟨1⟩ ""

def isStrLit? (stx : Syntax) : Option String :=
  match isLit? strLitKind stx with
  | some val => decodeStrLit val
  | _        => none

def decodeCharLit (s : String) : Option Char := do
  let c := s.get ⟨1⟩
  if c == '\\' then do
    let (c, _) ← decodeQuotedChar s ⟨2⟩
    pure c
  else
    pure c

def isCharLit? (stx : Syntax) : Option Char :=
  match isLit? charLitKind stx with
  | some val => decodeCharLit val
  | _        => none

private partial def splitNameLitAux (ss : Substring) (acc : List Substring) : List Substring :=
  let splitRest (ss : Substring) (acc : List Substring) : List Substring :=
    if ss.front == '.' then
      splitNameLitAux (ss.drop 1) acc
    else if ss.isEmpty then
      acc
    else
      []
  if ss.isEmpty then []
  else
    let curr := ss.front
    if isIdBeginEscape curr then
      let escapedPart := ss.takeWhile (!isIdEndEscape ·)
      let escapedPart := { escapedPart with stopPos := ss.stopPos.min (escapedPart.str.next escapedPart.stopPos) }
      if !isIdEndEscape (escapedPart.get <| escapedPart.prev ⟨escapedPart.bsize⟩) then []
      else splitRest (ss.extract ⟨escapedPart.bsize⟩ ⟨ss.bsize⟩) (escapedPart :: acc)
    else if isIdFirst curr then
      let idPart := ss.takeWhile isIdRest
      splitRest (ss.extract ⟨idPart.bsize⟩ ⟨ss.bsize⟩) (idPart :: acc)
    else if curr.isDigit then
      let idPart := ss.takeWhile Char.isDigit
      splitRest (ss.extract ⟨idPart.bsize⟩ ⟨ss.bsize⟩) (idPart :: acc)
    else
      []

/-- Split a name literal (without the backtick) into its dot-separated components. For example,
`foo.bla.«bo.o»` ↦ `["foo", "bla", "«bo.o»"]`. If the literal cannot be parsed, return `[]`. -/
def splitNameLit (ss : Substring) : List Substring :=
  splitNameLitAux ss [] |>.reverse

def _root_.Substring.toName (s : Substring) : Name :=
  match splitNameLitAux s [] with
  | [] => .anonymous
  | comps => comps.foldr (init := Name.anonymous)
    fun comp n =>
      let comp := comp.toString
      if isIdBeginEscape comp.front then
        Name.mkStr n (comp.drop 1 |>.dropRight 1)
      else if comp.front.isDigit then
        if let some k := decodeNatLitVal? comp then
          Name.mkNum n k
        else
          unreachable!
      else
        Name.mkStr n comp

def _root_.String.toName (s : String) : Name :=
  s.toSubstring.toName

def decodeNameLit (s : String) : Option Name :=
  if s.get 0 == '`' then
    match (s.toSubstring.drop 1).toName with
    | .anonymous => none
    | name => some name
  else
    none

def isNameLit? (stx : Syntax) : Option Name :=
  match isLit? nameLitKind stx with
  | some val => decodeNameLit val
  | _        => none

def hasArgs : Syntax → Bool
  | Syntax.node _ _ args => args.size > 0
  | _                    => false

def isAtom : Syntax → Bool
  | atom _ _ => true
  | _        => false

def isToken (token : String) : Syntax → Bool
  | atom _ val => val.trim == token.trim
  | _          => false

def isNone (stx : Syntax) : Bool :=
  match stx with
  | Syntax.node _ k args => k == nullKind && args.size == 0
  -- when elaborating partial syntax trees, it's reasonable to interpret missing parts as `none`
  | Syntax.missing     => true
  | _                  => false

def getOptionalIdent? (stx : Syntax) : Option Name :=
  match stx.getOptional? with
  | some stx => some stx.getId
  | none     => none

partial def findAux (p : Syntax → Bool) : Syntax → Option Syntax
  | stx@(Syntax.node _ _ args) => if p stx then some stx else args.findSome? (findAux p)
  | stx                        => if p stx then some stx else none

def find? (stx : Syntax) (p : Syntax → Bool) : Option Syntax :=
  findAux p stx

end Syntax

namespace TSyntax

def getNat (s : NumLit) : Nat :=
  s.raw.isNatLit?.getD 0

def getId (s : Ident) : Name :=
  s.raw.getId

def getScientific (s : ScientificLit) : Nat × Bool × Nat :=
  s.raw.isScientificLit?.getD (0, false, 0)

def getString (s : StrLit) : String :=
  s.raw.isStrLit?.getD ""

def getChar (s : CharLit) : Char :=
  s.raw.isCharLit?.getD default

def getName (s : NameLit) : Name :=
  s.raw.isNameLit?.getD .anonymous

def getHygieneInfo (s : HygieneInfo) : Name :=
  s.raw[0].getId

namespace Compat

scoped instance : CoeTail (Array Syntax) (Syntax.TSepArray k sep) where
  coe a := (a : TSyntaxArray k)

end Compat

end TSyntax

def HygieneInfo.mkIdent (s : HygieneInfo) (val : Name) (canonical := false) : Ident :=
  let src := s.raw[0]
  let id := { extractMacroScopes src.getId with name := val.eraseMacroScopes }.review
  ⟨Syntax.ident (SourceInfo.fromRef src canonical) (toString val).toSubstring id []⟩

/-- Reflect a runtime datum back to surface syntax (best-effort). -/
class Quote (α : Type) (k : SyntaxNodeKind := `term) where
  quote : α → TSyntax k

export Quote (quote)

set_option synthInstance.checkSynthOrder false in
instance [Quote α k] [CoeHTCT (TSyntax k) (TSyntax [k'])] : Quote α k' := ⟨fun a => quote (k := k) a⟩

instance : Quote Term := ⟨id⟩
instance : Quote Bool := ⟨fun | true => mkCIdent ``Bool.true | false => mkCIdent ``Bool.false⟩
instance : Quote String strLitKind := ⟨Syntax.mkStrLit⟩
instance : Quote Nat numLitKind := ⟨fun n => Syntax.mkNumLit <| toString n⟩
instance : Quote Substring := ⟨fun s => Syntax.mkCApp ``String.toSubstring' #[quote s.toString]⟩

-- in contrast to `Name.toString`, we can, and want to be, precise here
private def getEscapedNameParts? (acc : List String) : Name → Option (List String)
  | Name.anonymous => if acc.isEmpty then none else some acc
  | Name.str n s => do
    let s ← Name.escapePart s
    getEscapedNameParts? (s::acc) n
  | Name.num _ _ => none

def quoteNameMk : Name → Term
  | .anonymous => mkCIdent ``Name.anonymous
  | .str n s => Syntax.mkCApp ``Name.mkStr #[quoteNameMk n, quote s]
  | .num n i => Syntax.mkCApp ``Name.mkNum #[quoteNameMk n, quote i]

instance : Quote Name `term where
  quote n := match getEscapedNameParts? [] n with
    | some ss => ⟨mkNode `Lean.Parser.Term.quotedName #[Syntax.mkNameLit ("`" ++ ".".intercalate ss)]⟩
    | none    => ⟨quoteNameMk n⟩

instance [Quote α `term] [Quote β `term] : Quote (α × β) `term where
  quote
    | ⟨a, b⟩ => Syntax.mkCApp ``Prod.mk #[quote a, quote b]

private def quoteList [Quote α `term] : List α → Term
  | []      => mkCIdent ``List.nil
  | (x::xs) => Syntax.mkCApp ``List.cons #[quote x, quoteList xs]

instance [Quote α `term] : Quote (List α) `term where
  quote := quoteList

private def quoteArray [Quote α `term] (xs : Array α) : Term :=
  if xs.size <= 8 then
    go 0 #[]
  else
    Syntax.mkCApp ``List.toArray #[quote xs.toList]
where
  go (i : Nat) (args : Array Term) : Term :=
    if h : i < xs.size then
      go (i+1) (args.push (quote xs[i]))
    else
      Syntax.mkCApp (Name.mkStr2 "Array" ("mkArray" ++ toString xs.size)) args
termination_by go i _ => xs.size - i

instance [Quote α `term] : Quote (Array α) `term where
  quote := quoteArray

instance Option.hasQuote {α : Type} [Quote α `term] : Quote (Option α) `term where
  quote
    | none     => mkIdent ``none
    | (some x) => Syntax.mkCApp ``some #[quote x]


/-- Evaluator for `prec` DSL -/
def evalPrec (stx : Syntax) : MacroM Nat :=
  Macro.withIncRecDepth stx do
    let stx ← expandMacros stx
    match stx with
    | `(prec| $num:num) => return num.getNat
    | _ => Macro.throwErrorAt stx "unexpected precedence"

macro_rules
  | `(prec| $a + $b) => do `(prec| $(quote <| (← evalPrec a) + (← evalPrec b)):num)

macro_rules
  | `(prec| $a - $b) => do `(prec| $(quote <| (← evalPrec a) - (← evalPrec b)):num)

macro "eval_prec " p:prec:max : term => return quote (k := `term) (← evalPrec p)

/-- Evaluator for `prio` DSL -/
def evalPrio (stx : Syntax) : MacroM Nat :=
  Macro.withIncRecDepth stx do
    let stx ← expandMacros stx
    match stx with
    | `(prio| $num:num) => return num.getNat
    | _ => Macro.throwErrorAt stx "unexpected priority"

macro_rules
  | `(prio| $a + $b) => do `(prio| $(quote <| (← evalPrio a) + (← evalPrio b)):num)

macro_rules
  | `(prio| $a - $b) => do `(prio| $(quote <| (← evalPrio a) - (← evalPrio b)):num)

macro "eval_prio " p:prio:max : term => return quote (k := `term) (← evalPrio p)

def evalOptPrio : Option (TSyntax `prio) → MacroM Nat
  | some prio => evalPrio prio
  | none      => return 1000 -- TODO: FIX back eval_prio default

end Lean

namespace Array

abbrev getSepElems := @getEvenElems

open Lean

private partial def filterSepElemsMAux {m : Type → Type} [Monad m] (a : Array Syntax) (p : Syntax → m Bool) (i : Nat) (acc : Array Syntax) : m (Array Syntax) := do
  if h : i < a.size then
    let stx := a[i]
    if (← p stx) then
      if acc.isEmpty then
        filterSepElemsMAux a p (i+2) (acc.push stx)
      else if hz : i ≠ 0 then
        have : i.pred < i := Nat.pred_lt hz
        have : i.pred < a.size := Nat.lt_trans this h
        let sepStx := a[i.pred]
        filterSepElemsMAux a p (i+2) ((acc.push sepStx).push stx)
      else
        filterSepElemsMAux a p (i+2) (acc.push stx)
    else
      filterSepElemsMAux a p (i+2) acc
  else
    pure acc

def filterSepElemsM {m : Type → Type} [Monad m] (a : Array Syntax) (p : Syntax → m Bool) : m (Array Syntax) :=
  filterSepElemsMAux a p 0 #[]

def filterSepElems (a : Array Syntax) (p : Syntax → Bool) : Array Syntax :=
  Id.run <| a.filterSepElemsM p

private partial def mapSepElemsMAux {m : Type → Type} [Monad m] (a : Array Syntax) (f : Syntax → m Syntax) (i : Nat) (acc : Array Syntax) : m (Array Syntax) := do
  if h : i < a.size then
    let stx := a[i]
    if i % 2 == 0 then do
      let stx ← f stx
      mapSepElemsMAux a f (i+1) (acc.push stx)
    else
      mapSepElemsMAux a f (i+1) (acc.push stx)
  else
    pure acc

def mapSepElemsM {m : Type → Type} [Monad m] (a : Array Syntax) (f : Syntax → m Syntax) : m (Array Syntax) :=
  mapSepElemsMAux a f 0 #[]

def mapSepElems (a : Array Syntax) (f : Syntax → Syntax) : Array Syntax :=
  Id.run <| a.mapSepElemsM f

end Array

namespace Lean.Syntax

def SepArray.getElems (sa : SepArray sep) : Array Syntax :=
  sa.elemsAndSeps.getSepElems

def TSepArray.getElems (sa : TSepArray k sep) : TSyntaxArray k :=
  .mk sa.elemsAndSeps.getSepElems

def TSepArray.push (sa : TSepArray k sep) (e : TSyntax k) : TSepArray k sep :=
  if sa.elemsAndSeps.isEmpty then
    { elemsAndSeps := #[e] }
  else
    { elemsAndSeps := sa.elemsAndSeps.push (mkAtom sep) |>.push e }

instance : EmptyCollection (SepArray sep) where
  emptyCollection := ⟨∅⟩

instance : EmptyCollection (TSepArray sep k) where
  emptyCollection := ⟨∅⟩

instance : CoeOut (SepArray sep) (Array Syntax) where
  coe := SepArray.getElems

instance : CoeOut (TSepArray k sep) (TSyntaxArray k) where
  coe := TSepArray.getElems

instance [Coe (TSyntax k) (TSyntax k')] : Coe (TSyntaxArray k) (TSyntaxArray k') where
  coe a := a.map Coe.coe

instance : CoeOut (TSyntaxArray k) (Array Syntax) where
  coe a := a.raw

instance : Coe Ident (TSyntax `Lean.Parser.Command.declId) where
  coe id := mkNode _ #[id, mkNullNode #[]]

instance : Coe (Lean.Term) (Lean.TSyntax `Lean.Parser.Term.funBinder) where
  coe stx := ⟨stx⟩

end Lean.Syntax

set_option linter.unusedVariables.funArgs false in
/--
  Gadget for automatic parameter support. This is similar to the `optParam` gadget, but it uses
  the given tactic.
  Like `optParam`, this gadget only affects elaboration.
  For example, the tactic will *not* be invoked during type class resolution. -/
abbrev autoParam.{u} (α : Sort u) (tactic : Lean.Syntax) : Sort u := α

/-! # Helper functions for manipulating interpolated strings -/

namespace Lean.Syntax

private def decodeInterpStrQuotedChar (s : String) (i : String.Pos) : Option (Char × String.Pos) := do
  match decodeQuotedChar s i with
  | some r => some r
  | none   =>
    let c := s.get i
    let i := s.next i
    if c == '{' then pure ('{', i)
    else none

private partial def decodeInterpStrLit (s : String) : Option String :=
  let rec loop (i : String.Pos) (acc : String) : Option String :=
    let c := s.get i
    let i := s.next i
    if c == '\"' || c == '{' then
      pure acc
    else if s.atEnd i then
      none
    else if c == '\\' then do
      let (c, i) ← decodeInterpStrQuotedChar s i
      loop i (acc.push c)
    else
      loop i (acc.push c)
  loop ⟨1⟩ ""

partial def isInterpolatedStrLit? (stx : Syntax) : Option String :=
  match isLit? interpolatedStrLitKind stx with
  | none     => none
  | some val => decodeInterpStrLit val

def getSepArgs (stx : Syntax) : Array Syntax :=
  stx.getArgs.getSepElems

end Syntax

namespace TSyntax

def expandInterpolatedStrChunks (chunks : Array Syntax) (mkAppend : Syntax → Syntax → MacroM Syntax) (mkElem : Syntax → MacroM Syntax) : MacroM Syntax := do
  let mut i := 0
  let mut result := Syntax.missing
  for elem in chunks do
    let elem ← match elem.isInterpolatedStrLit? with
      | none     => mkElem elem
      | some str => mkElem (Syntax.mkStrLit str)
    if i == 0 then
      result := elem
    else
      result ← mkAppend result elem
    i := i+1
  return result

open TSyntax.Compat in
def expandInterpolatedStr (interpStr : TSyntax interpolatedStrKind) (type : Term) (toTypeFn : Term) : MacroM Term := do
  let r ← expandInterpolatedStrChunks interpStr.raw.getArgs (fun a b => `($a ++ $b)) (fun a => `($toTypeFn $a))
  `(($r : $type))

end TSyntax

namespace Meta

deriving instance Repr for TransparencyMode, EtaStructMode, DSimp.Config, Simp.Config

def Occurrences.contains : Occurrences → Nat → Bool
  | all,      _   => true
  | pos idxs, idx => idxs.contains idx
  | neg idxs, idx => !idxs.contains idx

def Occurrences.isAll : Occurrences → Bool
  | all => true
  | _   => false

namespace Rewrite

structure Config where
  transparency : TransparencyMode := TransparencyMode.reducible
  offsetCnstrs : Bool := true
  occs : Occurrences := Occurrences.all

end Rewrite

end Meta

namespace Parser.Tactic

/-- `erw [rules]` is a shorthand for `rw (config := { transparency := .default }) [rules]`.
This does rewriting up to unfolding of regular definitions (by comparison to regular `rw`
which only unfolds `@[reducible]` definitions). -/
macro "erw" s:rwRuleSeq loc:(location)? : tactic =>
  `(tactic| rw (config := { transparency := .default }) $s $(loc)?)

syntax simpAllKind := atomic(" (" &"all") " := " &"true" ")"
syntax dsimpKind   := atomic(" (" &"dsimp") " := " &"true" ")"

macro (name := declareSimpLikeTactic) doc?:(docComment)?
    "declare_simp_like_tactic" opt:((simpAllKind <|> dsimpKind)?)
    ppSpace tacName:ident ppSpace tacToken:str ppSpace updateCfg:term : command => do
  let (kind, tkn, stx) ←
    if opt.raw.isNone then
      pure (← `(``simp), ← `("simp"), ← `($[$doc?:docComment]? syntax (name := $tacName) $tacToken:str (config)? (discharger)? (&" only")? (" [" (simpStar <|> simpErase <|> simpLemma),* "]")? (location)? : tactic))
    else if opt.raw[0].getKind == ``simpAllKind then
      pure (← `(``simpAll), ← `("simp_all"), ← `($[$doc?:docComment]? syntax (name := $tacName) $tacToken:str (config)? (discharger)? (&" only")? (" [" (simpErase <|> simpLemma),* "]")? : tactic))
    else
      pure (← `(``dsimp), ← `("dsimp"), ← `($[$doc?:docComment]? syntax (name := $tacName) $tacToken:str (config)? (discharger)? (&" only")? (" [" (simpErase <|> simpLemma),* "]")? (location)? : tactic))
  `($stx:command
    @[macro $tacName] def expandSimp : Macro := fun s => do
      let c ← match s[1][0] with
        | `(config| (config := $$c)) => `(config| (config := $updateCfg $$c))
        | _ => `(config| (config := $updateCfg {}))
      let s := s.setKind $kind
      let s := s.setArg 0 (mkAtomFrom s[0] $tkn (canonical := true))
      let r := s.setArg 1 (mkNullNode #[c])
      return r)

/-- `simp!` is shorthand for `simp` with `autoUnfold := true`.
This will rewrite with all equation lemmas, which can be used to
partially evaluate many definitions. -/
declare_simp_like_tactic simpAutoUnfold "simp! " fun (c : Lean.Meta.Simp.Config) => { c with autoUnfold := true }

/-- `simp_arith` is shorthand for `simp` with `arith := true` and `decide := true`.
This enables the use of normalization by linear arithmetic. -/
declare_simp_like_tactic simpArith "simp_arith " fun (c : Lean.Meta.Simp.Config) => { c with arith := true, decide := true }

/-- `simp_arith!` is shorthand for `simp_arith` with `autoUnfold := true`.
This will rewrite with all equation lemmas, which can be used to
partially evaluate many definitions. -/
declare_simp_like_tactic simpArithAutoUnfold "simp_arith! " fun (c : Lean.Meta.Simp.Config) => { c with arith := true, autoUnfold := true, decide := true }

/-- `simp_all!` is shorthand for `simp_all` with `autoUnfold := true`.
This will rewrite with all equation lemmas, which can be used to
partially evaluate many definitions. -/
declare_simp_like_tactic (all := true) simpAllAutoUnfold "simp_all! " fun (c : Lean.Meta.Simp.ConfigCtx) => { c with autoUnfold := true }

/-- `simp_all_arith` combines the effects of `simp_all` and `simp_arith`. -/
declare_simp_like_tactic (all := true) simpAllArith "simp_all_arith " fun (c : Lean.Meta.Simp.ConfigCtx) => { c with arith := true, decide := true }

/-- `simp_all_arith!` combines the effects of `simp_all`, `simp_arith` and `simp!`. -/
declare_simp_like_tactic (all := true) simpAllArithAutoUnfold "simp_all_arith! " fun (c : Lean.Meta.Simp.ConfigCtx) => { c with arith := true, autoUnfold := true, decide := true }

/-- `dsimp!` is shorthand for `dsimp` with `autoUnfold := true`.
This will rewrite with all equation lemmas, which can be used to
partially evaluate many definitions. -/
declare_simp_like_tactic (dsimp := true) dsimpAutoUnfold "dsimp! " fun (c : Lean.Meta.DSimp.Config) => { c with autoUnfold := true }

end Parser.Tactic

end Lean
