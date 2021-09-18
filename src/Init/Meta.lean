/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura and Sebastian Ullrich

Additional goodies for writing macros
-/
prelude
import Init.Data.Array.Basic

namespace Lean

@[extern c inline "lean_box(LEAN_VERSION_MAJOR)"]
private constant version.getMajor (u : Unit) : Nat
def version.major : Nat := version.getMajor ()

@[extern c inline "lean_box(LEAN_VERSION_MINOR)"]
private constant version.getMinor (u : Unit) : Nat
def version.minor : Nat := version.getMinor ()

@[extern c inline "lean_box(LEAN_VERSION_PATCH)"]
private constant version.getPatch (u : Unit) : Nat
def version.patch : Nat := version.getPatch ()

-- @[extern c inline "lean_mk_string(LEAN_GITHASH)"]
-- constant getGithash (u : Unit) : String
-- def githash : String := getGithash ()

@[extern c inline "LEAN_VERSION_IS_RELEASE"]
constant version.getIsRelease (u : Unit) : Bool
def version.isRelease : Bool := version.getIsRelease ()

/-- Additional version description like "nightly-2018-03-11" -/
@[extern c inline "lean_mk_string(LEAN_SPECIAL_VERSION_DESC)"]
constant version.getSpecialDesc (u : Unit) : String
def version.specialDesc : String := version.getSpecialDesc ()


/- Valid identifier names -/
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
  | n@(str anonymous _ _) => n
  | n@(num anonymous _ _) => n
  | str n _ _             => getRoot n
  | num n _ _             => getRoot n

@[export lean_is_inaccessible_user_name]
def isInaccessibleUserName : Name → Bool
  | Name.str _ s _   => s.contains '✝' || s == "_inaccessible"
  | Name.num p idx _ => isInaccessibleUserName p
  | _                => false

def escapePart (s : String) : Option String :=
  if s.length > 0 && isIdFirst s[0] && (s.toSubstring.drop 1).all isIdRest then s
  else if s.any isIdEndEscape then none
  else some <| idBeginEscape.toString ++ s ++ idEndEscape.toString

-- NOTE: does not roundtrip even with `escape = true` if name is anonymous or contains numeric part or `idEndEscape`
variable (sep : String) (escape : Bool)
def toStringWithSep : Name → String
  | anonymous         => "[anonymous]"
  | str anonymous s _ => maybeEscape s
  | num anonymous v _ => toString v
  | str n s _         => toStringWithSep n ++ sep ++ maybeEscape s
  | num n v _         => toStringWithSep n ++ sep ++ Nat.repr v
where
  maybeEscape s := if escape then escapePart s |>.getD s else s

protected def toString (n : Name) (escape := true) : String :=
  -- never escape "prettified" inaccessible names or macro scopes or pseudo-syntax introduced by the delaborator
  toStringWithSep "." (escape && !n.isInaccessibleUserName && !n.hasMacroScopes && !maybePseudoSyntax) n
where
  maybePseudoSyntax :=
    if let Name.str _ s _ := n.getRoot then
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
  | num p i _ => Repr.addAppParen ("Lean.Name.mkNum " ++ Name.reprPrec p max_prec ++ " " ++ repr i) prec
  | str p s _ =>
    if p.hasNum then
      Repr.addAppParen ("Lean.Name.mkStr " ++ Name.reprPrec p max_prec ++ " " ++ repr s) prec
    else
      Std.Format.text "`" ++ n.toString

instance : Repr Name where
  reprPrec := Name.reprPrec

deriving instance Repr for Syntax

def capitalize : Name → Name
  | Name.str p s _ => Name.mkStr p s.capitalize
  | n              => n

def replacePrefix : Name → Name → Name → Name
  | anonymous,     anonymous, newP => newP
  | anonymous,     _,         _    => anonymous
  | n@(str p s _), queryP,    newP => if n == queryP then newP else Name.mkStr (p.replacePrefix queryP newP) s
  | n@(num p s _), queryP,    newP => if n == queryP then newP else Name.mkNum (p.replacePrefix queryP newP) s

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
    | str p s _ => Name.mkStr p (s ++ suffix)
    | n         => Name.mkStr n suffix

@[export lean_name_append_index_after]
def appendIndexAfter (n : Name) (idx : Nat) : Name :=
  n.modifyBase fun
    | str p s _ => Name.mkStr p (s ++ "_" ++ toString idx)
    | n         => Name.mkStr n ("_" ++ toString idx)

@[export lean_name_append_before]
def appendBefore (n : Name) (pre : String) : Name :=
  n.modifyBase fun
    | anonymous => Name.mkStr anonymous pre
    | str p s _ => Name.mkStr p (pre ++ s)
    | num p n _ => Name.mkNum (Name.mkStr p pre) n

end Name

structure NameGenerator where
  namePrefix : Name := `_uniq
  idx        : Nat  := 1
  deriving Inhabited

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

partial def structEq : Syntax → Syntax → Bool
  | Syntax.missing, Syntax.missing => true
  | Syntax.node k args, Syntax.node k' args' => k == k' && args.isEqv args' structEq
  | Syntax.atom _ val, Syntax.atom _ val' => val == val'
  | Syntax.ident _ rawVal val preresolved, Syntax.ident _ rawVal' val' preresolved' => rawVal == rawVal' && val == val' && preresolved == preresolved'
  | _, _ => false

instance : BEq Lean.Syntax := ⟨structEq⟩

partial def getTailInfo? : Syntax → Option SourceInfo
  | atom info _   => info
  | ident info .. => info
  | node _ args   => args.findSomeRev? getTailInfo?
  | _             => none

def getTailInfo (stx : Syntax) : SourceInfo :=
  stx.getTailInfo?.getD SourceInfo.none

def getTrailingSize (stx : Syntax) : Nat :=
  match stx.getTailInfo? with
  | some (SourceInfo.original (trailing := trailing) ..) => trailing.bsize
  | _ => 0

@[specialize] private partial def updateLast {α} [Inhabited α] (a : Array α) (f : α → Option α) (i : Nat) : Option (Array α) :=
  if i == 0 then
    none
  else
    let i := i - 1
    let v := a[i]
    match f v with
    | some v => some <| a.set! i v
    | none   => updateLast a f i

partial def setTailInfoAux (info : SourceInfo) : Syntax → Option Syntax
  | atom _ val             => some <| atom info val
  | ident _ rawVal val pre => some <| ident info rawVal val pre
  | node k args            =>
    match updateLast args (setTailInfoAux info) args.size with
    | some args => some <| node k args
    | none      => none
  | stx                    => none

def setTailInfo (stx : Syntax) (info : SourceInfo) : Syntax :=
  match setTailInfoAux info stx with
  | some stx => stx
  | none     => stx

def unsetTrailing (stx : Syntax) : Syntax :=
  match stx.getTailInfo with
  | SourceInfo.original lead pos trail endPos => stx.setTailInfo (SourceInfo.original lead pos "".toSubstring endPos)
  | _                                         => stx

@[specialize] private partial def updateFirst {α} [Inhabited α] (a : Array α) (f : α → Option α) (i : Nat) : Option (Array α) :=
  if h : i < a.size then
    let v := a.get ⟨i, h⟩;
    match f v with
    | some v => some <| a.set ⟨i, h⟩ v
    | none   => updateFirst a f (i+1)
  else
    none

partial def setHeadInfoAux (info : SourceInfo) : Syntax → Option Syntax
  | atom _ val             => some <| atom info val
  | ident _ rawVal val pre => some <| ident info rawVal val pre
  | node k args            =>
    match updateFirst args (setHeadInfoAux info) 0 with
    | some args => some <| node k args
    | noxne     => none
  | stx                    => none

def setHeadInfo (stx : Syntax) (info : SourceInfo) : Syntax :=
  match setHeadInfoAux info stx with
  | some stx => stx
  | none     => stx

def setInfo (info : SourceInfo) : Syntax → Syntax
  | atom _ val             => atom info val
  | ident _ rawVal val pre => ident info rawVal val pre
  | stx                    => stx

/-- Return the first atom/identifier that has position information -/
partial def getHead? : Syntax → Option Syntax
  | stx@(atom info ..)  => info.getPos?.map fun _ => stx
  | stx@(ident info ..) => info.getPos?.map fun _ => stx
  | node _ args      => args.findSome? getHead?
  | _                => none

def copyHeadTailInfoFrom (target source : Syntax) : Syntax :=
  target.setHeadInfo source.getHeadInfo |>.setTailInfo source.getTailInfo

end Syntax

/-- Use the head atom/identifier of the current `ref` as the `ref` -/
@[inline] def withHeadRefOnly {m : Type → Type} [Monad m] [MonadRef m] {α} (x : m α) : m α := do
  match (← getRef).getHead? with
  | none => x
  | some ref => withRef ref x

@[inline] def mkNode (k : SyntaxNodeKind) (args : Array Syntax) : Syntax :=
  Syntax.node k args

/- Syntax objects for a Lean module. -/
structure Module where
  header   : Syntax
  commands : Array Syntax

/-- Expand all macros in the given syntax -/
partial def expandMacros : Syntax → MacroM Syntax
  | stx@(Syntax.node k args) => do
    match (← expandMacro? stx) with
    | some stxNew => expandMacros stxNew
    | none        => do
      let args ← Macro.withIncRecDepth stx <| args.mapM expandMacros
      pure <| Syntax.node k args
  | stx => pure stx

/- Helper functions for processing Syntax programmatically -/

/--
  Create an identifier copying the position from `src`.
  To refer to a specific constant, use `mkCIdentFrom` instead. -/
def mkIdentFrom (src : Syntax) (val : Name) : Syntax :=
  Syntax.ident (SourceInfo.fromRef src) (toString val).toSubstring val []

def mkIdentFromRef [Monad m] [MonadRef m] (val : Name) : m Syntax := do
  return mkIdentFrom (← getRef) val

/--
  Create an identifier referring to a constant `c` copying the position from `src`.
  This variant of `mkIdentFrom` makes sure that the identifier cannot accidentally
  be captured. -/
def mkCIdentFrom (src : Syntax) (c : Name) : Syntax :=
  -- Remark: We use the reserved macro scope to make sure there are no accidental collision with our frontend
  let id   := addMacroScope `_internal c reservedMacroScope
  Syntax.ident (SourceInfo.fromRef src) (toString id).toSubstring id [(c, [])]

def mkCIdentFromRef [Monad m] [MonadRef m] (c : Name) : m Syntax := do
  return mkCIdentFrom (← getRef) c

def mkCIdent (c : Name) : Syntax :=
  mkCIdentFrom Syntax.missing c

@[export lean_mk_syntax_ident]
def mkIdent (val : Name) : Syntax :=
  Syntax.ident SourceInfo.none (toString val).toSubstring val []

@[inline] def mkNullNode (args : Array Syntax := #[]) : Syntax :=
  Syntax.node nullKind args

@[inline] def mkGroupNode (args : Array Syntax := #[]) : Syntax :=
  Syntax.node groupKind args

def mkSepArray (as : Array Syntax) (sep : Syntax) : Array Syntax := do
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
  | some arg => Syntax.node nullKind #[arg]
  | none     => Syntax.node nullKind #[]

def mkHole (ref : Syntax) : Syntax :=
  Syntax.node `Lean.Parser.Term.hole #[mkAtomFrom ref "_"]

namespace Syntax

def mkSep (a : Array Syntax) (sep : Syntax) : Syntax :=
  mkNullNode <| mkSepArray a sep

def SepArray.ofElems {sep} (elems : Array Syntax) : SepArray sep :=
⟨mkSepArray elems (mkAtom sep)⟩

def SepArray.ofElemsUsingRef [Monad m] [MonadRef m] {sep} (elems : Array Syntax) : m (SepArray sep) := do
  let ref ← getRef;
  return ⟨mkSepArray elems (mkAtomFrom ref sep)⟩

instance (sep) : Coe (Array Syntax) (SepArray sep) where
  coe := SepArray.ofElems

/-- Create syntax representing a Lean term application, but avoid degenerate empty applications. -/
def mkApp (fn : Syntax) : (args : Array Syntax) → Syntax
  | #[]  => fn
  | args => Syntax.node `Lean.Parser.Term.app #[fn, mkNullNode args]

def mkCApp (fn : Name) (args : Array Syntax) : Syntax :=
  mkApp (mkCIdent fn) args

def mkLit (kind : SyntaxNodeKind) (val : String) (info := SourceInfo.none) : Syntax :=
  let atom : Syntax := Syntax.atom info val
  Syntax.node kind #[atom]

def mkStrLit (val : String) (info := SourceInfo.none) : Syntax :=
  mkLit strLitKind (String.quote val) info

def mkNumLit (val : String) (info := SourceInfo.none) : Syntax :=
  mkLit numLitKind val info

def mkScientificLit (val : String) (info := SourceInfo.none) : Syntax :=
  mkLit scientificLitKind val info

def mkNameLit (val : String) (info := SourceInfo.none) : Syntax :=
  mkLit nameLitKind val info

/- Recall that we don't have special Syntax constructors for storing numeric and string atoms.
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
        let c := s.get 1
        if c == 'x' || c == 'X' then decodeHexLitAux s 2 0
        else if c == 'b' || c == 'B' then decodeBinLitAux s 2 0
        else if c == 'o' || c == 'O' then decodeOctalLitAux s 2 0
        else if c.isDigit then decodeDecimalLitAux s 0 0
        else none
    else if c.isDigit then decodeDecimalLitAux s 0 0
    else none

def isLit? (litKind : SyntaxNodeKind) (stx : Syntax) : Option String :=
  match stx with
  | Syntax.node k args =>
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
    let c := s.get i
    if c == '-' then
       decodeAfterExp (s.next i) val e true 0
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

def decodeQuotedChar (s : String) (i : String.Pos) : Option (Char × String.Pos) :=
  OptionM.run do
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

partial def decodeStrLitAux (s : String) (i : String.Pos) (acc : String) : Option String :=
  OptionM.run do
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
  decodeStrLitAux s 1 ""

def isStrLit? (stx : Syntax) : Option String :=
  match isLit? strLitKind stx with
  | some val => decodeStrLit val
  | _        => none

def decodeCharLit (s : String) : Option Char :=
  OptionM.run do
    let c := s.get 1
    if c == '\\' then do
      let (c, _) ← decodeQuotedChar s 2
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
      if !isIdEndEscape (escapedPart.get <| escapedPart.prev escapedPart.bsize) then []
      else splitRest (ss.extract escapedPart.bsize ss.bsize) (escapedPart :: acc)
    else if isIdFirst curr then
      let idPart := ss.takeWhile isIdRest
      splitRest (ss.extract idPart.bsize ss.bsize) (idPart :: acc)
    else if curr.isDigit then
      let idPart := ss.takeWhile Char.isDigit
      splitRest (ss.extract idPart.bsize ss.bsize) (idPart :: acc)
    else
      []

/-- Split a name literal (without the backtick) into its dot-separated components. For example,
`foo.bla.«bo.o»` ↦ `["foo", "bla", "«bo.o»"]`. If the literal cannot be parsed, return `[]`. -/
def splitNameLit (ss : Substring) : List Substring :=
  splitNameLitAux ss [] |>.reverse

def decodeNameLit (s : String) : Option Name :=
  if s.get 0 == '`' then
    match splitNameLitAux (s.toSubstring.drop 1) [] with
    | [] => none
    | comps => some <| comps.foldr (init := Name.anonymous)
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
  else
    none

def isNameLit? (stx : Syntax) : Option Name :=
  match isLit? nameLitKind stx with
  | some val => decodeNameLit val
  | _        => none

def hasArgs : Syntax → Bool
  | Syntax.node _ args => args.size > 0
  | _                  => false

def isAtom : Syntax → Bool
  | atom _ _ => true
  | _        => false

def isToken (token : String) : Syntax → Bool
  | atom _ val => val.trim == token.trim
  | _          => false

def isNone (stx : Syntax) : Bool :=
  match stx with
  | Syntax.node k args => k == nullKind && args.size == 0
  -- when elaborating partial syntax trees, it's reasonable to interpret missing parts as `none`
  | Syntax.missing     => true
  | _                  => false

def getOptional? (stx : Syntax) : Option Syntax :=
  match stx with
  | Syntax.node k args => if k == nullKind && args.size == 1 then some (args.get! 0) else none
  | _                  => none

def getOptionalIdent? (stx : Syntax) : Option Name :=
  match stx.getOptional? with
  | some stx => some stx.getId
  | none     => none

partial def findAux (p : Syntax → Bool) : Syntax → Option Syntax
  | stx@(Syntax.node _ args) => if p stx then some stx else args.findSome? (findAux p)
  | stx                      => if p stx then some stx else none

def find? (stx : Syntax) (p : Syntax → Bool) : Option Syntax :=
  findAux p stx

end Syntax

/-- Reflect a runtime datum back to surface syntax (best-effort). -/
class Quote (α : Type) where
  quote : α → Syntax

export Quote (quote)

instance : Quote Syntax := ⟨id⟩
instance : Quote Bool := ⟨fun | true => mkCIdent `Bool.true | false => mkCIdent `Bool.false⟩
instance : Quote String := ⟨Syntax.mkStrLit⟩
instance : Quote Nat := ⟨fun n => Syntax.mkNumLit <| toString n⟩
instance : Quote Substring := ⟨fun s => Syntax.mkCApp `String.toSubstring #[quote s.toString]⟩

-- in contrast to `Name.toString`, we can, and want to be, precise here
private def getEscapedNameParts? (acc : List String) : Name → OptionM (List String)
  | Name.anonymous => acc
  | Name.str n s _ => do
    let s ← Name.escapePart s
    getEscapedNameParts? (s::acc) n
  | Name.num n i _ => none

private def quoteNameMk : Name → Syntax
  | Name.anonymous => mkCIdent ``Name.anonymous
  | Name.str n s _ => Syntax.mkCApp ``Name.mkStr #[quoteNameMk n, quote s]
  | Name.num n i _ => Syntax.mkCApp ``Name.mkNum #[quoteNameMk n, quote i]

instance : Quote Name where
  quote n := match getEscapedNameParts? [] n with
    | some ss => mkNode `Lean.Parser.Term.quotedName #[Syntax.mkNameLit ("`" ++ ".".intercalate ss)]
    | none    => quoteNameMk n

instance {α β : Type} [Quote α] [Quote β] : Quote (α × β) where
  quote
    | ⟨a, b⟩ => Syntax.mkCApp ``Prod.mk #[quote a, quote b]

private def quoteList {α : Type} [Quote α] : List α → Syntax
  | []      => mkCIdent ``List.nil
  | (x::xs) => Syntax.mkCApp ``List.cons #[quote x, quoteList xs]

instance {α : Type} [Quote α] : Quote (List α) where
  quote := quoteList

instance {α : Type} [Quote α] : Quote (Array α) where
  quote xs := Syntax.mkCApp ``List.toArray #[quote xs.toList]

private def quoteOption {α : Type} [Quote α] : Option α → Syntax
  | none     => mkIdent ``none
  | (some x) => Syntax.mkCApp ``some #[quote x]

instance Option.hasQuote {α : Type} [Quote α] : Quote (Option α) where
  quote := quoteOption

/- Evaluator for `prec` DSL -/
def evalPrec (stx : Syntax) : MacroM Nat :=
  Macro.withIncRecDepth stx do
    let stx ← expandMacros stx
    match stx with
    | `(prec| $num:numLit) => return num.isNatLit?.getD 0
    | _ => Macro.throwErrorAt stx "unexpected precedence"

macro_rules
  | `(prec| $a + $b) => do `(prec| $(quote <| (← evalPrec a) + (← evalPrec b)):numLit)

macro_rules
  | `(prec| $a - $b) => do `(prec| $(quote <| (← evalPrec a) - (← evalPrec b)):numLit)

macro "eval_prec " p:prec:max : term => return quote (← evalPrec p)

/- Evaluator for `prio` DSL -/
def evalPrio (stx : Syntax) : MacroM Nat :=
  Macro.withIncRecDepth stx do
    let stx ← expandMacros stx
    match stx with
    | `(prio| $num:numLit) => return num.isNatLit?.getD 0
    | _ => Macro.throwErrorAt stx "unexpected priority"

macro_rules
  | `(prio| $a + $b) => do `(prio| $(quote <| (← evalPrio a) + (← evalPrio b)):numLit)

macro_rules
  | `(prio| $a - $b) => do `(prio| $(quote <| (← evalPrio a) - (← evalPrio b)):numLit)

macro "eval_prio " p:prio:max : term => return quote (← evalPrio p)

def evalOptPrio : Option Syntax → MacroM Nat
  | some prio => evalPrio prio
  | none      => return eval_prio default

end Lean

namespace Array

abbrev getSepElems := @getEvenElems

open Lean

private partial def filterSepElemsMAux {m : Type → Type} [Monad m] (a : Array Syntax) (p : Syntax → m Bool) (i : Nat) (acc : Array Syntax) : m (Array Syntax) := do
  if h : i < a.size then
    let stx := a.get ⟨i, h⟩
    if (← p stx) then
      if acc.isEmpty then
        filterSepElemsMAux a p (i+2) (acc.push stx)
      else if hz : i ≠ 0 then
        have : i.pred < i := Nat.pred_lt hz
        let sepStx := a.get ⟨i.pred, Nat.lt_trans this h⟩
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
    let stx := a.get ⟨i, h⟩
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

namespace Lean.Syntax.SepArray

def getElems {sep} (sa : SepArray sep) : Array Syntax :=
  sa.elemsAndSeps.getSepElems

/-
We use `CoeTail` here instead of `Coe` to avoid a "loop" when computing `CoeTC`.
The "loop" is interrupted using the maximum instance size threshold, but it is a performance bottleneck.
The loop occurs because the predicate `isNewAnswer` is too imprecise.
-/
instance (sep) : CoeTail (SepArray sep) (Array Syntax) where
  coe := getElems

end Lean.Syntax.SepArray

/--
  Gadget for automatic parameter support. This is similar to the `optParam` gadget, but it uses
  the given tactic.
  Like `optParam`, this gadget only affects elaboration.
  For example, the tactic will *not* be invoked during type class resolution. -/
abbrev autoParam.{u} (α : Sort u) (tactic : Lean.Syntax) : Sort u := α

/- Helper functions for manipulating interpolated strings -/
namespace Lean.Syntax

private def decodeInterpStrQuotedChar (s : String) (i : String.Pos) : Option (Char × String.Pos) :=
  OptionM.run do
    match decodeQuotedChar s i with
    | some r => some r
    | none   =>
      let c := s.get i
      let i := s.next i
      if c == '{' then pure ('{', i)
      else none

private partial def decodeInterpStrLit (s : String) : Option String :=
  let rec loop (i : String.Pos) (acc : String) : OptionM String :=
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
  loop 1 ""

partial def isInterpolatedStrLit? (stx : Syntax) : Option String :=
  match isLit? interpolatedStrLitKind stx with
  | none     => none
  | some val => decodeInterpStrLit val

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

def expandInterpolatedStr (interpStr : Syntax) (type : Syntax) (toTypeFn : Syntax) : MacroM Syntax := do
  let ref := interpStr
  let r ← expandInterpolatedStrChunks interpStr.getArgs (fun a b => `($a ++ $b)) (fun a => `($toTypeFn $a))
  `(($r : $type))

def getSepArgs (stx : Syntax) : Array Syntax :=
  stx.getArgs.getSepElems

end Syntax

namespace Meta

inductive TransparencyMode where
  | all | default | reducible | instances
  deriving Inhabited, BEq, Repr

namespace Simp

def defaultMaxSteps := 100000

structure Config where
  maxSteps          : Nat  := defaultMaxSteps
  maxDischargeDepth : Nat  := 2
  contextual        : Bool := false
  memoize           : Bool := true
  singlePass        : Bool := false
  zeta              : Bool := true
  beta              : Bool := true
  eta               : Bool := true
  iota              : Bool := true
  proj              : Bool := true
  decide            : Bool := true
  deriving Inhabited, BEq, Repr

-- Configuration object for `simp_all`
structure ConfigCtx extends Config where
  contextual := true

end Simp

namespace Rewrite

structure Config where
  transparency : TransparencyMode := TransparencyMode.reducible
  offsetCnstrs : Bool := true

end Rewrite

end Meta

namespace Parser.Tactic

macro "erw " s:rwRuleSeq loc:(location)? : tactic =>
  `(rw (config := { transparency := Lean.Meta.TransparencyMode.default }) $s:rwRuleSeq $[$(loc.getOptional?):location]?)

end Parser.Tactic

end Lean
