/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Dany Fabian
-/

import Lean.Data.Parsec
import Lean.Data.Xml.Basic
open IO
open System
open Lean

namespace Lean
namespace Xml

namespace Parser
open Lean.Parsec
open Parsec.ParseResult

abbrev LeanChar := Char

/-- consume a newline character sequence pretending, that we read '\n'. As per spec:
  https://www.w3.org/TR/xml/#sec-line-ends -/
def endl : Parsec LeanChar := (skipString "\r\n" <|> skipChar '\r' <|> skipChar '\n') *> pure '\n'

def quote (p : Parsec α) : Parsec α :=
  skipChar '\'' *> p <* skipChar '\''
  <|> skipChar '"' *> p <* skipChar '"'

/-- https://www.w3.org/TR/xml/#NT-Char -/
def Char : Parsec LeanChar :=
  (attempt do
  let c ← anyChar
  let cNat := c.toNat
  if (0x20 ≤ cNat ∧ cNat ≤ 0xD7FF)
   ∨ (0xE000 ≤ cNat ∧ cNat ≤ 0xFFFD)
   ∨ (0x10000 ≤ cNat ∧ cNat ≤ 0x10FFFF) then pure c else fail "expected xml char")
  <|> pchar '\t' <|> endl

/-- https://www.w3.org/TR/xml/#NT-S -/
def S : Parsec String :=
  many1Chars (pchar ' ' <|> endl <|> pchar '\t')

/-- https://www.w3.org/TR/xml/#NT-Eq -/
def Eq : Parsec Unit :=
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
def NameStartChar : Parsec LeanChar := attempt do
  let c ← anyChar
  if ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z') then pure c
  else if c = ':' ∨ c = '_' then pure c
  else
    let cNum := c.toNat
    if nameStartCharRanges.any (fun (lo, hi) => lo ≤ cNum ∧ cNum ≤ hi) then pure c
    else fail "expected a name character"

/-- https://www.w3.org/TR/xml/#NT-NameChar -/
def NameChar : Parsec LeanChar :=
  NameStartChar <|> digit <|> pchar '-' <|> pchar '.' <|> pchar '\xB7'
  <|> satisfy (λ c => ('\u0300' ≤ c ∧ c ≤ '\u036F') ∨ ('\u203F' ≤ c ∧ c ≤ '\u2040'))

/-- https://www.w3.org/TR/xml/#NT-Name -/
def Name : Parsec String := do
  let x ← NameStartChar
  manyCharsCore NameChar x.toString

/-- https://www.w3.org/TR/xml/#NT-VersionNum -/
def VersionNum : Parsec Unit :=
  skipString "1." <* (many1 digit)

/-- https://www.w3.org/TR/xml/#NT-VersionInfo -/
def VersionInfo : Parsec Unit := do
  S *>
  skipString "version"
  Eq
  quote VersionNum

/-- https://www.w3.org/TR/xml/#NT-EncName -/
def EncName : Parsec String := do
  let x ← asciiLetter
  manyCharsCore (asciiLetter <|> digit <|> pchar '-' <|> pchar '_' <|> pchar '.') x.toString

/-- https://www.w3.org/TR/xml/#NT-EncodingDecl -/
def EncodingDecl : Parsec String := do
  S *>
  skipString "encoding"
  Eq
  quote EncName

/-- https://www.w3.org/TR/xml/#NT-SDDecl -/
def SDDecl : Parsec String := do
  S *> skipString "standalone" *> Eq *> quote (pstring "yes" <|> pstring "no")

/-- https://www.w3.org/TR/xml/#NT-XMLDecl -/
def XMLdecl : Parsec Unit := do
  skipString "<?xml"
  VersionInfo
  optional EncodingDecl *>
  optional SDDecl *>
  optional S *>
  skipString "?>"

/-- https://www.w3.org/TR/xml/#NT-Comment -/
def Comment : Parsec String :=
  let notDash := Char.toString <$> satisfy (λ c => c ≠ '-')
  skipString "<!--" *>
  Array.foldl String.append "" <$> many (attempt <| notDash <|> (do
    let d ← pchar '-'
    let c ← notDash
    pure $ d.toString ++ c))
  <* skipString "-->"

/-- https://www.w3.org/TR/xml/#NT-PITarget -/
def PITarget : Parsec String :=
  Name <* (skipChar 'X' <|> skipChar 'x') <* (skipChar 'M' <|> skipChar 'm') <* (skipChar 'L' <|> skipChar 'l')

/-- https://www.w3.org/TR/xml/#NT-PI -/
def PI : Parsec Unit := do
  skipString "<?"
  <* PITarget <*
  optional (S *> manyChars (notFollowedBy (skipString "?>") *> Char))
  skipString "?>"

/-- https://www.w3.org/TR/xml/#NT-Misc -/
def Misc : Parsec Unit :=
  Comment *> pure () <|> PI <|> S *> pure ()

/-- https://www.w3.org/TR/xml/#NT-SystemLiteral -/
def SystemLiteral : Parsec String :=
  pchar '"' *> manyChars (satisfy λ c => c ≠ '"') <* pchar '"'
  <|> pchar '\'' *> manyChars (satisfy λ c => c ≠ '\'') <* pure '\''

/-- https://www.w3.org/TR/xml/#NT-PubidChar -/
def PubidChar : Parsec LeanChar :=
  asciiLetter <|> digit <|> endl <|> attempt do
  let c ← anyChar
  if "-'()+,./:=?;!*#@$_%".contains c then pure c else fail "PublidChar expected"

/-- https://www.w3.org/TR/xml/#NT-PubidLiteral -/
def PubidLiteral : Parsec String :=
  pchar '"' *> manyChars PubidChar <* pchar '"'
  <|> pchar '\'' *> manyChars (attempt do
    let c ← PubidChar
    if c = '\'' then fail "'\\'' not expected" else pure c) <* pchar '\''

/-- https://www.w3.org/TR/xml/#NT-ExternalID -/
def ExternalID : Parsec Unit :=
  skipString "SYSTEM" *> S *> SystemLiteral *> pure ()
  <|> skipString "PUBLIC" *> S *> PubidLiteral *> S *> SystemLiteral *> pure ()

/-- https://www.w3.org/TR/xml/#NT-Mixed -/
def Mixed : Parsec Unit :=
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
  partial def cp : Parsec Unit :=
    (Name *> pure () <|> choice <|> seq) <* optional (skipChar '?' <|> skipChar '*' <|> skipChar '+')

  /-- https://www.w3.org/TR/xml/#NT-choice -/
  partial def choice : Parsec Unit := do
    skipChar '('
    optional S *>
    cp
    many1 (optional S *> skipChar '|' *> optional S *> cp) *>
    optional S *>
    skipChar ')'

  /-- https://www.w3.org/TR/xml/#NT-seq -/
  partial def seq : Parsec Unit := do
    skipChar '('
    optional S *>
    cp
    many (optional S *> skipChar ',' *> optional S *> cp) *>
    optional S *>
    skipChar ')'
end

/-- https://www.w3.org/TR/xml/#NT-children -/
def children : Parsec Unit :=
  (choice <|> seq) <* optional (skipChar '?' <|> skipChar '*' <|> skipChar '+')

/-- https://www.w3.org/TR/xml/#NT-contentspec -/
def contentspec : Parsec Unit := do
  skipString "EMPTY" <|> skipString "ANY" <|> Mixed <|> children

/-- https://www.w3.org/TR/xml/#NT-elementdecl -/
def elementDecl : Parsec Unit := do
  skipString "<!ELEMENT"
  S *>
  Name *>
  contentspec *>
  optional S *>
  skipChar '>'

/-- https://www.w3.org/TR/xml/#NT-StringType -/
def StringType : Parsec Unit :=
  skipString "CDATA"

/-- https://www.w3.org/TR/xml/#NT-TokenizedType -/
def TokenizedType : Parsec Unit :=
  skipString "ID"
  <|> skipString "IDREF"
  <|> skipString "IDREFS"
  <|> skipString "ENTITY"
  <|> skipString "ENTITIES"
  <|> skipString "NMTOKEN"
  <|> skipString "NMTOKENS"

/-- https://www.w3.org/TR/xml/#NT-NotationType -/
def NotationType : Parsec Unit := do
  skipString "NOTATION"
  S *>
  skipChar '(' <*
  optional S
  Name *> many (optional S *> skipChar '|' *> optional S *> Name) *>
  optional S *>
  skipChar ')'

/-- https://www.w3.org/TR/xml/#NT-Nmtoken -/
def Nmtoken : Parsec String := do
  many1Chars NameChar

/-- https://www.w3.org/TR/xml/#NT-Enumeration -/
def Enumeration : Parsec Unit := do
  skipChar '('
  optional S *>
  Nmtoken *> many (optional S *> skipChar '|' *> optional S *> Nmtoken) *>
  optional S *>
  skipChar ')'

/-- https://www.w3.org/TR/xml/#NT-EnumeratedType -/
def EnumeratedType : Parsec Unit :=
  NotationType <|> Enumeration

/-- https://www.w3.org/TR/xml/#NT-AttType -/
def AttType : Parsec Unit :=
  StringType <|> TokenizedType <|> EnumeratedType

def predefinedEntityToChar : String → Option LeanChar
| "lt" => some '<'
| "gt" => some '>'
| "amp" => some '&'
| "apos" => some '\''
| "quot" => some '"'
| _ => none

/-- https://www.w3.org/TR/xml/#NT-EntityRef -/
def EntityRef : Parsec $ Option LeanChar := attempt $
  skipChar '&' *> predefinedEntityToChar <$> Name <* skipChar ';'

@[inline]
def hexDigitToNat (c : LeanChar) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

def digitsToNat (base : Nat) (digits : Array Nat) : Nat :=
  digits.foldl (λ r d => r * base + d) 0

/-- https://www.w3.org/TR/xml/#NT-CharRef -/
def CharRef : Parsec LeanChar := do
  skipString "&#"
  let charCode ←
    digitsToNat 10 <$> many1 (hexDigitToNat <$> digit)
    <|> skipChar 'x' *> digitsToNat 16 <$> many1 (hexDigitToNat <$> hexDigit)
  skipChar ';'
  return Char.ofNat charCode

/-- https://www.w3.org/TR/xml/#NT-Reference -/
def Reference : Parsec $ Option LeanChar :=
  EntityRef <|> some <$> CharRef

/-- https://www.w3.org/TR/xml/#NT-AttValue -/
def AttValue : Parsec String := do
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
def DefaultDecl : Parsec Unit :=
  skipString "#REQUIRED"
  <|> skipString "#IMPLIED"
  <|> optional (skipString "#FIXED" <* S) *> AttValue *> pure ()

/-- https://www.w3.org/TR/xml/#NT-AttDef -/
def AttDef : Parsec Unit :=
  S *> Name *> S *> AttType *> S *> DefaultDecl

/-- https://www.w3.org/TR/xml/#NT-AttlistDecl -/
def AttlistDecl : Parsec Unit :=
  skipString "<!ATTLIST" *> S *> Name *> many AttDef *> optional S *> skipChar '>'

/-- https://www.w3.org/TR/xml/#NT-PEReference -/
def PEReference : Parsec Unit :=
  skipChar '%' *> Name *> skipChar ';'

/-- https://www.w3.org/TR/xml/#NT-EntityValue -/
def EntityValue : Parsec String := do
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
def NDataDecl : Parsec Unit :=
  S *> skipString "NDATA" <* S <* Name

/-- https://www.w3.org/TR/xml/#NT-EntityDef -/
def EntityDef : Parsec Unit :=
  EntityValue *> pure () <|> (ExternalID <* optional NDataDecl)

/-- https://www.w3.org/TR/xml/#NT-GEDecl -/
def GEDecl : Parsec Unit :=
  skipString "<!ENTITY" *> S *> Name *> S *> EntityDef *> optional S *> skipChar '>'

/-- https://www.w3.org/TR/xml/#NT-PEDef -/
def PEDef : Parsec Unit :=
  EntityValue *> pure () <|> ExternalID

/-- https://www.w3.org/TR/xml/#NT-PEDecl -/
def PEDecl : Parsec Unit :=
  skipString "<!ENTITY" *> S *> skipChar '%' *> S *> Name *> PEDef *> optional S *> skipChar '>'

/-- https://www.w3.org/TR/xml/#NT-EntityDecl -/
def EntityDecl : Parsec Unit :=
  GEDecl <|> PEDecl

/-- https://www.w3.org/TR/xml/#NT-PublicID -/
def PublicID : Parsec Unit :=
  skipString "PUBLIC" <* S <* PubidLiteral

/-- https://www.w3.org/TR/xml/#NT-NotationDecl -/
def NotationDecl : Parsec Unit :=
  skipString "<!NOTATION" *> S *> Name *> (ExternalID <|> PublicID) *> optional S *> skipChar '>'

/-- https://www.w3.org/TR/xml/#NT-markupdecl -/
def markupDecl : Parsec Unit :=
  elementDecl <|> AttlistDecl <|> EntityDecl <|> NotationDecl <|> PI <|> (Comment *> pure ())

/-- https://www.w3.org/TR/xml/#NT-DeclSep -/
def DeclSep : Parsec Unit :=
  PEReference <|> S *> pure ()

/-- https://www.w3.org/TR/xml/#NT-intSubset -/
def intSubset : Parsec Unit :=
  many (markupDecl <|> DeclSep) *> pure ()

/-- https://www.w3.org/TR/xml/#NT-doctypedecl -/
def doctypedecl : Parsec Unit := do
  skipString "<!DOCTYPE"
  S *>
  Name *>
  optional (S *> ExternalID) *> pure ()
  <* optional S
  optional (skipChar '[' *> intSubset <* skipChar ']' <* optional S) *>
  skipChar '>'

/-- https://www.w3.org/TR/xml/#NT-prolog -/
def prolog : Parsec Unit :=
  optional XMLdecl *>
  many Misc *>
  optional (doctypedecl <* many Misc) *> pure ()

/-- https://www.w3.org/TR/xml/#NT-Attribute -/
def Attribute : Parsec (String × String) := do
  let name ← Name
  Eq
  let value ← AttValue
  return (name, value)

protected def elementPrefix : Parsec (Array Content → Element) := do
  skipChar '<'
  let name ← Name
  let attributes ← many (attempt <| S *> Attribute)
  optional S *> pure ()
  return Element.Element name (RBMap.fromList attributes.toList compare)

/-- https://www.w3.org/TR/xml/#NT-EmptyElemTag -/
def EmptyElemTag (elem : Array Content → Element) : Parsec Element := do
  skipString "/>" *> pure (elem #[])

/-- https://www.w3.org/TR/xml/#NT-STag -/
def STag (elem : Array Content → Element) : Parsec (Array Content → Element) := do
  skipChar '>' *> pure elem

/-- https://www.w3.org/TR/xml/#NT-ETag -/
def ETag : Parsec Unit :=
  skipString "</" *> Name *> optional S *> skipChar '>'

/-- https://www.w3.org/TR/xml/#NT-CDStart -/
def CDStart : Parsec Unit :=
  skipString "<![CDATA["

/-- https://www.w3.org/TR/xml/#NT-CDEnd -/
def CDEnd : Parsec Unit :=
  skipString "]]>"

/-- https://www.w3.org/TR/xml/#NT-CData -/
def CData : Parsec String :=
  manyChars (notFollowedBy (skipString "]]>") *> anyChar)

/-- https://www.w3.org/TR/xml/#NT-CDSect -/
def CDSect : Parsec String :=
  CDStart *> CData <* CDEnd

/-- https://www.w3.org/TR/xml/#NT-CharData -/
def CharData : Parsec String :=
  notFollowedBy (skipString "]]>") *> manyChars (satisfy λ c => c ≠ '<' ∧ c ≠ '&')

mutual
  /-- https://www.w3.org/TR/xml/#NT-content -/
  partial def content : Parsec (Array Content) := do
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
    let xs := #[x] ++ xs.concatMap id |>.filterMap id
    let mut res := #[]
    for x in xs do
      if res.size > 0 then
        match res.back, x with
        | Content.Character x, Content.Character y => res := res.set! (res.size - 1) (Content.Character $ x ++ y)
        | _, x => res := res.push x
      else res := res.push x
    return res

  /-- https://www.w3.org/TR/xml/#NT-element -/
  partial def element : Parsec Element := do
    let elem ← Parser.elementPrefix
    EmptyElemTag elem <|> STag elem <*> content <* ETag

end

/-- https://www.w3.org/TR/xml/#NT-document -/
def document : Parsec Element := prolog *> element <* many Misc <* eof

end Parser

def parse (s : String) : Except String Element :=
  match Xml.Parser.document s.mkIterator with
  | Parsec.ParseResult.success _ res => Except.ok res
  | Parsec.ParseResult.error it err  => Except.error s!"offset {it.i.byteIdx.repr}: {err}\n{(it.prevn 10).extract it}"

end Xml
