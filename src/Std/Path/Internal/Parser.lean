/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Path.Component
public import Std.Internal.Parsec.String

public section

/-!
# Path.Parser

POSIX and Windows path parsers for `Std.Path`.
-/

namespace Std.Path.Internal

open Std.Internal.Parsec Std.Internal.Parsec.String

private def classifySegment (s : String) : Path.Component :=
  if s == ".." then .parent
  else if s == "." then .current
  else .normal s

private def isWinSep (c : Char) : Bool :=
  c == '\\' || c == '/'

private def parseDrive : Parser String :=
  attempt do
    let c ← satisfy Char.isAlpha
    discard <| pchar ':'
    return String.singleton c ++ ":"

private def posixSeg : Parser Path.Component :=
  many1Chars (satisfy (· != '/')) <&> classifySegment

private def winSegString : Parser String :=
  many1Chars (satisfy (fun c => !isWinSep c))

/--
Like `winSegString` but also matches an empty segment, for the prefix bodies that are already
identified by the marker introducing them.
-/
private def winSegStringOpt : Parser String :=
  manyChars (satisfy (fun c => !isWinSep c))

private def winSeg : Parser Path.Component :=
  winSegString <&> classifySegment

/--
Parse the `server` and optional `share` of a UNC prefix, after whatever introduces it.
-/
private def parseShare : Parser (String × String) := do
  let server ← winSegString
  let share ← attempt (satisfy isWinSep *> winSegString) <|> pure ""
  return (server, share)

/--
Parse the body of a verbatim prefix, after the introducing `\\?\`.
-/
private def parseVerbatimBody : Parser Path.Prefix :=
  attempt (do
    discard <| pstring "UNC"
    discard <| satisfy isWinSep
    let (server, share) ← parseShare
    return .verbatimUNC server share) <|>
  attempt (.verbatimDisk <$> parseDrive) <|>
  (.verbatim <$> winSegStringOpt)

/--
Parse a `\\`-introduced prefix: a verbatim path, a device path, or a UNC share.

A bare `\\` is not one, and is left to be parsed as a root, keeping `\\` and `\` equivalent as they
are on Windows itself.
-/
private def parseDoubleSepPrefix : Parser Path.Prefix := do
  discard <| satisfy isWinSep
  discard <| satisfy isWinSep
  attempt (do
    discard <| pchar '?'
    discard <| satisfy isWinSep
    parseVerbatimBody) <|>
  attempt (do
    discard <| pchar '.'
    discard <| satisfy isWinSep
    .deviceNS <$> winSegStringOpt) <|>
  (do
    let (server, share) ← parseShare
    return .unc server share)

private def parsePrefix : Parser (Option Path.Prefix) :=
  attempt (some <$> parseDoubleSepPrefix) <|>
  attempt (some <$> (.disk <$> parseDrive)) <|>
  pure none

def posixPathParser : Parser (Array Path.Component) := do
  let hasRoot ← flag (pchar '/')
  discard <| manyChars (attempt (pchar '/'))

  let init := if hasRoot then #[.root "/"] else #[]

  match ← optional posixSeg with
  | none =>
    return init
  | some first =>
    let rest ← many (attempt (many1Chars (pchar '/') *> posixSeg))
    discard <| manyChars (pchar '/')
    return init ++ #[first] ++ rest

def windowsPathParser : Parser (Array Path.Component) := do
  let pfx ← parsePrefix
  let prefixInit := pfx.elim #[] (#[.winPrefix ·])
  let hasRoot ← flag (satisfy isWinSep)
  discard <| manyChars (attempt (satisfy isWinSep))

  let init := if hasRoot then prefixInit.push (.root "\\") else prefixInit

  match ← optional winSeg with
  | none =>
    return init
  | some first =>
    let rest ← many (attempt (many1Chars (satisfy isWinSep) *> winSeg))
    discard <| manyChars (satisfy isWinSep)
    return init ++ #[first] ++ rest

end Std.Path.Internal
