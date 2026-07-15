/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Util.Log
import Lake.Util.JsonObject
import Lake.Util.Proc
import Init.Data.String.TakeDrop
import Init.Data.String.Search
import Init.TacticsExtra  -- shake: keep (out-of-line macro_rules def, fix)

open Lean

namespace Lake

public def hexEncodeByte (b : UInt8) : Char :=
  if b = 0 then '0' else
  if b = 1 then '1' else
  if b = 2 then '2' else
  if b = 3 then '3' else
  if b = 4 then '4' else
  if b = 5 then '5' else
  if b = 6 then '6' else
  if b = 7 then '7' else
  if b = 8 then '8' else
  if b = 9 then '9' else
  if b = 0xa then 'A' else
  if b = 0xb then 'B' else
  if b = 0xc then 'C' else
  if b = 0xd then 'D' else
  if b = 0xe then 'E' else
  if b = 0xf then 'F' else
  '*'

/-- Encode a byte as a URI escape code (e.g., `%20`). -/
public def uriEscapeByte (b : UInt8) (s := "") : String :=
  s.push '%' |>.push (hexEncodeByte <| b >>> 4) |>.push (hexEncodeByte <| b &&& 0xF)

/-- Folds a monadic function over the UTF-8 bytes of `Char` from most significant to least significant. -/
@[specialize] public def foldlUtf8M [Monad m] (c : Char) (f : σ → UInt8 → m σ) (init : σ) : m σ := do
  let s := init
  let v := c.val
  if v ≤ 0x7f then
    f s v.toUInt8
  else if v ≤ 0x7ff then
    let s ← f s <| (v >>>  6).toUInt8 &&& 0x1f ||| 0xc0
    let s ← f s <| v.toUInt8 &&& 0x3f ||| 0x80
    return s
  else if v ≤ 0xffff then
    let s ← f s <| (v >>> 12).toUInt8 &&& 0x0f ||| 0xe0
    let s ← f s <| (v >>>  6).toUInt8 &&& 0x3f ||| 0x80
    let s ← f s <| v.toUInt8 &&& 0x3f ||| 0x80
    return s
  else
    let s ← f s <| (v >>> 18).toUInt8 &&& 0x07 ||| 0xf0
    let s ← f s <| (v >>> 12).toUInt8 &&& 0x3f ||| 0x80
    let s ← f s <| (v >>>  6).toUInt8 &&& 0x3f ||| 0x80
    let s ← f s <| v.toUInt8 &&& 0x3f ||| 0x80
    return s

public abbrev foldlUtf8 (c : Char) (f : σ → UInt8 → σ) (init : σ) : σ :=
  Id.run <| foldlUtf8M c (pure <| f · ·) init

example : foldlUtf8 c (fun l b => b::l) List.nil = (String.utf8EncodeChar c).reverse := by
  simp only [foldlUtf8, foldlUtf8M]
  simp only [String.utf8EncodeChar_eq_utf8EncodeCharFast, String.utf8EncodeCharFast]
  if h1 : c.val ≤ 0x7f then simp [h1]
  else if h2 : c.val ≤ 0x7ff then simp [h1, h2]
  else if h3 : c.val ≤ 0xffff then simp [h1, h2, h3]
  else simp [h1, h2, h3]

/-- Encode a character as a sequence of URI escape codes representing its UTF8 encoding. -/
public def uriEscapeChar (c : Char) (s := "") : String :=
  foldlUtf8 c (init := s) fun s b => uriEscapeByte b s

/--
A URI unreserved mark as specified in [RFC3986][2].
Unlike the older [RFC2396][1], RFC2396 also reserves `!`, `*`, `'`, `(`, and `)`.

Lake uses RFC3986 here because the `curl` implementation of AWS Sigv4
that Lake uses to upload artifacts requires these additional characters to be escaped.

[1]: https://datatracker.ietf.org/doc/html/rfc2396#section-2.3
[2]: https://datatracker.ietf.org/doc/html/rfc3986#section-2.3
-/
public def isUriUnreservedMark (c : Char)  : Bool :=
  c matches '-' | '_' | '.' | '~'

/-- Encodes anything but a URI unreserved character as a URI escape sequences. -/
public def uriEncodeChar (c : Char) (s := "") : String :=
  if c.isAlphanum || isUriUnreservedMark c then
    s.push c
  else
    uriEscapeChar c s

/-- Encodes a string as an ASCII URI component, escaping special characters (and unicode). -/
public def uriEncode (s : String) (init := "") : String :=
  s.foldl (init := init) fun s c => uriEncodeChar c s

/--
Performs a HTTP `GET` request of a URL (using `curl` with JSON output) and, if successful,
return the body.  Otherwise, returns `none` on a 404 and errors on anything else.
-/
public def getUrl?
  (url : String) (headers : Array String := #[])
: LogIO (Option String) := withLogErrorPos do
  let args := #[
      "-s", "-L", "-w", "%{stderr}%{json}\n",
      "--retry", "3" -- intermittent network errors can occur
  ]
  let args := headers.foldl (init := args) (· ++ #["-H", ·])
  let out ← captureProc' {cmd := "curl", args := args.push url}
  match Json.parse out.stderr >>= JsonObject.fromJson? with
  | .ok data =>
    let code ← id do
      match (data.get? "response_code" <|> data.get? "http_code") with
      | .ok (some code) => return code
      | .ok none => error s!"curl's JSON output did not contain a response code"
      | .error e => error s!"curl's JSON output contained an invalid JSON response code: {e}"
    if code == 200 then
      return some out.stdout.trimAscii.copy
    else if code == 404 then
      return none
    else
      error s!"failed to GET URL, error {code}; received:\n{out.stdout}"
  | .error e =>
    error s!"curl produced invalid JSON output: {e}"

/-- Perform a HTTP `GET` request of a URL (using `curl`) and return the body. -/
public def getUrl (url : String) (headers : Array String := #[]) : LogIO String := do
  let args := #[
      "-s", "-L",
      "--retry", "3" -- intermittent network errors can occur
  ]
  let args := headers.foldl (init := args) (· ++ #["-H", ·])
  captureProc {cmd := "curl", args := args.push url}
