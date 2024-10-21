/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Dany Fabian
-/
prelude
import Std.Internal.Parsec
import Lean.Data.Xml.Basic

open System
open Lean

namespace Lean
namespace Xml

open Std.Internal.Parsec
open Std.Internal.Parsec.String

namespace Parser

abbrev LeanChar := Char

/-- consume a newline character sequence pretending, that we read '\n'. As per spec:
  https://www.w3.org/TR/xml/#sec-line-ends -/
def endl : Parser LeanChar := (skipString "\r\n" <|> skipChar '\r' <|> skipChar '\n') *> pure '\n'

def quote (p : Parser α) : Parser α :=
  skipChar '\'' *> p <* skipChar '\''
  <|> skipChar '"' *> p <* skipChar '"'

/-- https://www.w3.org/TR/xml/#NT-Char -/
def Char : Parser LeanChar :=
  (attempt do
  let c ← any
  let cNat := c.toNat
  if (0x20 ≤ cNat ∧ cNat ≤ 0xD7FF)
   ∨ (0xE000 ≤ cNat ∧ cNat ≤ 0xFFFD)
   ∨ (0x10000 ≤ cNat ∧ cNat ≤ 0x10FFFF) then pure c else fail "expected xml char")
  <|> pchar '\t' <|> endl

/-- https://www.w3.org/TR/xml/#NT-S -/
def S : Parser String :=
  many1Chars (pchar ' ' <|> endl <|> pchar '\t')

/-- https://www.w3.org/TR/xml/#NT-Eq -/
def Eq : Parser Unit :=
  optional S *> skipChar '=' <* optional S

private def nameStartCharRanges : Array (Nat × Nat) :=
  #[(0xC0, 0xD6),
    (0xD8, 0xF6),
    (0xF8, 0x2FF),
    (0x370, 0x37D),
    (0x37F, 0x1FFF),
    (0x200C, 0x200D),
    (0x2070, 0x218F),
    (0x2C00, 0x2FEF),
    (0x3001, 0xD7FF),
    (0xF900, 0xFDCF),
    (0xFDF0, 0xFFFD),
    (0x10000, 0xEFFFF)]

/-- https://www.w3.org/TR/xml/#NT-NameStartChar -/
def NameStartChar : Parser LeanChar := attempt do
  let c ← any
  if ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z') then pure c
  else if c = ':' ∨ c = '_' then pure c
  else
    let cNum := c.toNat
    if nameStartCharRanges.any (fun (lo, hi) => lo ≤ cNum ∧ cNum ≤ hi) then pure c
    else fail "expected a name character"

/-- https://www.w3.org/TR/xml/#NT-NameChar -/
def NameChar : Parser LeanChar :=
  NameStartChar <|> digit <|> pchar '-' <|> pchar '.' <|> pchar '\xB7'
  <|> satisfy (λ c => ('\u0300' ≤ c ∧ c ≤ '\u036F') ∨ ('\u203F' ≤ c ∧ c ≤ '\u2040'))

/-- https://www.w3.org/TR/xml/#NT-Name -/
def Name : Parser String := do
  let x ← NameStartChar
  manyCharsCore NameChar x.toString

/-- https://www.w3.org/TR/xml/#NT-VersionNum -/
def VersionNum : Parser Unit :=
  skipString "1." <* (many1 digit)

/-- https://www.w3.org/TR/xml/#NT-VersionInfo -/
def VersionInfo : Parser Unit := do
  S *>
  skipString "version"
  Eq
  quote VersionNum

/-- https://www.w3.org/TR/xml/#NT-EncName -/
def EncName : Parser String := do
  let x ← asciiLetter
  manyCharsCore (asciiLetter <|> digit <|> pchar '-' <|> pchar '_' <|> pchar '.') x.toString

/-- https://www.w3.org/TR/xml/#NT-EncodingDecl -/
def EncodingDecl : Parser String := do
  S *>
  skipString "encoding"
  Eq
  quote EncName

/-- https://www.w3.org/TR/xml/#NT-SDDecl -/
def SDDecl : Parser String := do
  S *> skipString "standalone" *> Eq *> quote (pstring "yes" <|> pstring "no")

/-- https://www.w3.org/TR/xml/#NT-XMLDecl -/
def XMLdecl : Parser Unit := do
  skipString "<?xml"
  VersionInfo
  optional EncodingDecl *>
  optional SDDecl *>
  optional S *>
  skipString "?>"

/-- https://www.w3.org/TR/xml/#NT-Comment -/
def Comment : Parser String :=
  let notDash := Char.toString <$> satisfy (λ c => c ≠ '-')
  skipString "<!--" *>
  Array.foldl String.append "" <$> many (attempt <| notDash <|> (do
    let d ← pchar '-'
    let c ← notDash
    pure $ d.toString ++ c))
  <* skipString "-->"

/-- https://www.w3.org/TR/xml/#NT-PITarget -/
def PITarget : Parser String :=
  Name <* (skipChar 'X' <|> skipChar 'x') <* (skipChar 'M' <|> skipChar 'm') <* (skipChar 'L' <|> skipChar 'l')

/-- https://www.w3.org/TR/xml/#NT-PI -/
def PI : Parser Unit := do
  skipString "<?"
  <* PITarget <*
  optional (S *> manyChars (notFollowedBy (skipString "?>") *> Char))
  skipString "?>"

/-- https://www.w3.org/TR/xml/#NT-Misc -/
def Misc : Parser Unit :=
  Comment *> pure () <|> PI <|> S *> pure ()

/-- https://www.w3.org/TR/xml/#NT-SystemLiteral -/
def SystemLiteral : Parser String :=
  pchar '"' *> manyChars (satisfy λ c => c ≠ '"') <* pchar '"'
  <|> pchar '\'' *> manyChars (satisfy λ c => c ≠ '\'') <* pure '\''

/-- https://www.w3.org/TR/xml/#NT-PubidChar -/
def PubidChar : Parser LeanChar :=
  asciiLetter <|> digit <|> endl <|> attempt do
  let c ← any
  if "-'()+,./:=?;!*#@$_%".contains c then pure c else fail "PublidChar expected"

/-- https://www.w3.org/TR/xml/#NT-PubidLiteral -/
def PubidLiteral : Parser String :=
  pchar '"' *> manyChars PubidChar <* pchar '"'
  <|> pchar '\'' *> manyChars (attempt do
    let c ← PubidChar
    if c = '\'' then fail "'\\'' not expected" else pure c) <* pchar '\''

/-- https://www.w3.org/TR/xml/#NT-ExternalID -/
def ExternalID : Parser Unit :=
  skipString "SYSTEM" *> S *> SystemLiteral *> pure ()
  <|> skipString "PUBLIC" *> S *> PubidLiteral *> S *> SystemLiteral *> pure ()

/-- https://www.w3.org/TR/xml/#NT-Mixed -/
def Mixed : Parser Unit :=
  (do
    skipChar '('
    optional S *>
    skipString "#PCDATA" *>
    many (optional S *> skipChar '|' *> optional S *> Name) *>
    optional S *>
    skipString ")*")
  <|> skipChar '(' *> (optional S) *> skipString "#PCDATA" <* (optional S) <* skipChar ')'

mutual
  /-- https://www.w3.org/TR/xml/#NT-cp -/
  partial def cp : Parser Unit :=
    (Name *> pure () <|> choice <|> seq) <* optional (skipChar '?' <|> skipChar '*' <|> skipChar '+')

  /-- https://www.w3.org/TR/xml/#NT-choice -/
  partial def choice : Parser Unit := do
    skipChar '('
    optional S *>
    cp
    many1 (optional S *> skipChar '|' *> optional S *> cp) *>
    optional S *>
    skipChar ')'

  /-- https://www.w3.org/TR/xml/#NT-seq -/
  partial def seq : Parser Unit := do
    skipChar '('
    optional S *>
    cp
    many (optional S *> skipChar ',' *> optional S *> cp) *>
    optional S *>
    skipChar ')'
end

/-- https://www.w3.org/TR/xml/#NT-children -/
def children : Parser Unit :=
  (choice <|> seq) <* optional (skipChar '?' <|> skipChar '*' <|> skipChar '+')

/-- https://www.w3.org/TR/xml/#NT-contentspec -/
def contentspec : Parser Unit := do
  skipString "EMPTY" <|> skipString "ANY" <|> Mixed <|> children

/-- https://www.w3.org/TR/xml/#NT-elementdecl -/
def elementDecl : Parser Unit := do
  skipString "<!ELEMENT"
  S *>
  Name *>
  contentspec *>
  optional S *>
  skipChar '>'

/-- https://www.w3.org/TR/xml/#NT-StringType -/
def StringType : Parser Unit :=
  skipString "CDATA"

/-- https://www.w3.org/TR/xml/#NT-TokenizedType -/
def TokenizedType : Parser Unit :=
  skipString "ID"
  <|> skipString "IDREF"
  <|> skipString "IDREFS"
  <|> skipString "ENTITY"
  <|> skipString "ENTITIES"
  <|> skipString "NMTOKEN"
  <|> skipString "NMTOKENS"

/-- https://www.w3.org/TR/xml/#NT-NotationType -/
def NotationType : Parser Unit := do
  skipString "NOTATION"
  S *>
  skipChar '(' <*
  optional S
  Name *> many (optional S *> skipChar '|' *> optional S *> Name) *>
  optional S *>
  skipChar ')'

/-- https://www.w3.org/TR/xml/#NT-Nmtoken -/
def Nmtoken : Parser String := do
  many1Chars NameChar

/-- https://www.w3.org/TR/xml/#NT-Enumeration -/
def Enumeration : Parser Unit := do
  skipChar '('
  optional S *>
  Nmtoken *> many (optional S *> skipChar '|' *> optional S *> Nmtoken) *>
  optional S *>
  skipChar ')'

/-- https://www.w3.org/TR/xml/#NT-EnumeratedType -/
def EnumeratedType : Parser Unit :=
  NotationType <|> Enumeration

/-- https://www.w3.org/TR/xml/#NT-AttType -/
def AttType : Parser Unit :=
  StringType <|> TokenizedType <|> EnumeratedType

def predefinedEntityToChar : String → Option LeanChar
| "lt" => some '<'
| "gt" => some '>'
| "amp" => some '&'
| "apos" => some '\''
| "quot" => some '"'
| _ => none

/-- https://www.w3.org/TR/xml/#NT-EntityRef -/
def EntityRef : Parser $ Option LeanChar := attempt $
  skipChar '&' *> predefinedEntityToChar <$> Name <* skipChar ';'

@[inline]
def hexDigitToNat (c : LeanChar) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

def digitsToNat (base : Nat) (digits : Array Nat) : Nat :=
  digits.foldl (λ r d => r * base + d) 0

/-- https://www.w3.org/TR/xml/#NT-CharRef -/
def CharRef : Parser LeanChar := do
  skipString "&#"
  let charCode ←
    digitsToNat 10 <$> many1 (hexDigitToNat <$> digit)
    <|> skipChar 'x' *> digitsToNat 16 <$> many1 (hexDigitToNat <$> hexDigit)
  skipChar ';'
  return Char.ofNat charCode

/-- https://www.w3.org/TR/xml/#NT-Reference -/
def Reference : Parser $ Option LeanChar :=
  EntityRef <|> some <$> CharRef

/-- https://www.w3.org/TR/xml/#NT-AttValue -/
def AttValue : Parser String := do
  let chars ←
  (do
    skipChar '"'
    many (some <$> satisfy (λ c => c ≠ '<' ∧ c ≠ '&' ∧ c ≠ '"') <|> Reference) <*
    skipChar '"')
  <|> (do
    skipChar '\''
    many (some <$> satisfy (λ c => c ≠ '<' ∧ c ≠ '&' ∧ c ≠ '\'') <|> Reference) <*
    skipChar '\'')
  return chars.foldl (λ s c => if let some c := c then s.push c else s) ""

/-- https://www.w3.org/TR/xml/#NT-DefaultDecl -/
def DefaultDecl : Parser Unit :=
  skipString "#REQUIRED"
  <|> skipString "#IMPLIED"
  <|> optional (skipString "#FIXED" <* S) *> AttValue *> pure ()

/-- https://www.w3.org/TR/xml/#NT-AttDef -/
def AttDef : Parser Unit :=
  S *> Name *> S *> AttType *> S *> DefaultDecl

/-- https://www.w3.org/TR/xml/#NT-AttlistDecl -/
def AttlistDecl : Parser Unit :=
  skipString "<!ATTLIST" *> S *> Name *> many AttDef *> optional S *> skipChar '>'

/-- https://www.w3.org/TR/xml/#NT-PEReference -/
def PEReference : Parser Unit :=
  skipChar '%' *> Name *> skipChar ';'

/-- https://www.w3.org/TR/xml/#NT-EntityValue -/
def EntityValue : Parser String := do
  let chars ←
  (do
    skipChar '"'
    many (some <$> satisfy (λ c => c ≠ '%' ∧ c ≠ '&' ∧ c ≠ '"') <|> PEReference *> pure none <|> Reference) <*
    skipChar '"')
  <|> (do
    skipChar '\''
    many (some <$> satisfy (λ c => c ≠ '%' ∧ c ≠ '&' ∧ c ≠ '\'') <|> PEReference *> pure none <|> Reference) <*
    skipChar '\'')
  return chars.foldl (λ s c => if let some c := c then s.push c else s) ""


/-- https://www.w3.org/TR/xml/#NT-NDataDecl -/
def NDataDecl : Parser Unit :=
  S *> skipString "NDATA" <* S <* Name

/-- https://www.w3.org/TR/xml/#NT-EntityDef -/
def EntityDef : Parser Unit :=
  EntityValue *> pure () <|> (ExternalID <* optional NDataDecl)

/-- https://www.w3.org/TR/xml/#NT-GEDecl -/
def GEDecl : Parser Unit :=
  skipString "<!ENTITY" *> S *> Name *> S *> EntityDef *> optional S *> skipChar '>'

/-- https://www.w3.org/TR/xml/#NT-PEDef -/
def PEDef : Parser Unit :=
  EntityValue *> pure () <|> ExternalID

/-- https://www.w3.org/TR/xml/#NT-PEDecl -/
def PEDecl : Parser Unit :=
  skipString "<!ENTITY" *> S *> skipChar '%' *> S *> Name *> PEDef *> optional S *> skipChar '>'

/-- https://www.w3.org/TR/xml/#NT-EntityDecl -/
def EntityDecl : Parser Unit :=
  GEDecl <|> PEDecl

/-- https://www.w3.org/TR/xml/#NT-PublicID -/
def PublicID : Parser Unit :=
  skipString "PUBLIC" <* S <* PubidLiteral

/-- https://www.w3.org/TR/xml/#NT-NotationDecl -/
def NotationDecl : Parser Unit :=
  skipString "<!NOTATION" *> S *> Name *> (ExternalID <|> PublicID) *> optional S *> skipChar '>'

/-- https://www.w3.org/TR/xml/#NT-markupdecl -/
def markupDecl : Parser Unit :=
  elementDecl <|> AttlistDecl <|> EntityDecl <|> NotationDecl <|> PI <|> (Comment *> pure ())

/-- https://www.w3.org/TR/xml/#NT-DeclSep -/
def DeclSep : Parser Unit :=
  PEReference <|> S *> pure ()

/-- https://www.w3.org/TR/xml/#NT-intSubset -/
def intSubset : Parser Unit :=
  many (markupDecl <|> DeclSep) *> pure ()

/-- https://www.w3.org/TR/xml/#NT-doctypedecl -/
def doctypedecl : Parser Unit := do
  skipString "<!DOCTYPE"
  S *>
  Name *>
  optional (S *> ExternalID) *> pure ()
  <* optional S
  optional (skipChar '[' *> intSubset <* skipChar ']' <* optional S) *>
  skipChar '>'

/-- https://www.w3.org/TR/xml/#NT-prolog -/
def prolog : Parser Unit :=
  optional XMLdecl *>
  many Misc *>
  optional (doctypedecl <* many Misc) *> pure ()

/-- https://www.w3.org/TR/xml/#NT-Attribute -/
def Attribute : Parser (String × String) := do
  let name ← Name
  Eq
  let value ← AttValue
  return (name, value)

protected def elementPrefix : Parser (Array Content → Element) := do
  skipChar '<'
  let name ← Name
  let attributes ← many (attempt <| S *> Attribute)
  optional S *> pure ()
  return Element.Element name (RBMap.fromList attributes.toList compare)

/-- https://www.w3.org/TR/xml/#NT-EmptyElemTag -/
def EmptyElemTag (elem : Array Content → Element) : Parser Element := do
  skipString "/>" *> pure (elem #[])

/-- https://www.w3.org/TR/xml/#NT-STag -/
def STag (elem : Array Content → Element) : Parser (Array Content → Element) := do
  skipChar '>' *> pure elem

/-- https://www.w3.org/TR/xml/#NT-ETag -/
def ETag : Parser Unit :=
  skipString "</" *> Name *> optional S *> skipChar '>'

/-- https://www.w3.org/TR/xml/#NT-CDStart -/
def CDStart : Parser Unit :=
  skipString "<![CDATA["

/-- https://www.w3.org/TR/xml/#NT-CDEnd -/
def CDEnd : Parser Unit :=
  skipString "]]>"

/-- https://www.w3.org/TR/xml/#NT-CData -/
def CData : Parser String :=
  manyChars (notFollowedBy (skipString "]]>") *> any)

/-- https://www.w3.org/TR/xml/#NT-CDSect -/
def CDSect : Parser String :=
  CDStart *> CData <* CDEnd

/-- https://www.w3.org/TR/xml/#NT-CharData -/
def CharData : Parser String :=
  notFollowedBy (skipString "]]>") *> manyChars (satisfy λ c => c ≠ '<' ∧ c ≠ '&')

mutual
  /-- https://www.w3.org/TR/xml/#NT-content -/
  partial def content : Parser (Array Content) := do
    let x ← optional (Content.Character <$> CharData)
    let xs ← many do
      let y ←
        attempt (some <$> Content.Element <$> element)
        <|> (do let c ← Reference; pure <| c.map (Content.Character ∘ Char.toString))
        <|> some <$> Content.Character <$> CDSect
        <|> PI *> pure none
        <|> some <$> Content.Comment <$> Comment

      let z ← optional (Content.Character <$> CharData)
      pure #[y, z]
    let xs := #[x] ++ xs.flatMap id |>.filterMap id
    let mut res := #[]
    for x in xs do
      if res.size > 0 then
        match res.back, x with
        | Content.Character x, Content.Character y => res := res.set! (res.size - 1) (Content.Character $ x ++ y)
        | _, x => res := res.push x
      else res := res.push x
    return res

  /-- https://www.w3.org/TR/xml/#NT-element -/
  partial def element : Parser Element := do
    let elem ← Parser.elementPrefix
    EmptyElemTag elem <|> STag elem <*> content <* ETag

end

/-- https://www.w3.org/TR/xml/#NT-document -/
def document : Parser Element := prolog *> element <* many Misc <* eof

end Parser

def parse (s : String) : Except String Element :=
  Parser.run Xml.Parser.document s

end Xml
