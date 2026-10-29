/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.ToString
public import Std.Http.Internal
import Init.Data.String.Search
import Init.Data.String.Iter

public section

/-!
# Header Names

This module defines the `Name` type, which represents validated HTTP header names that conform to
HTTP standards.

Reference: https://www.rfc-editor.org/rfc/rfc9110.html#section-5
-/

namespace Std.Http.Header

set_option linter.all true

open Std.Http.Internal

/--
Proposition asserting that a string is a valid HTTP header name: all characters are valid token
characters and the string is non-empty.

Reference: https://www.rfc-editor.org/rfc/rfc9110.html#name-field-names
-/
abbrev IsValidHeaderName (s : String) : Prop :=
  isToken s

/--
A validated HTTP header name that ensures all characters conform to HTTP standards. Header names are
case-insensitive according to HTTP specifications.

Reference: https://www.rfc-editor.org/rfc/rfc9110.html#name-field-names
-/
@[ext]
structure Name where
  /--
  The lowercased normalized header name string.
  -/
  value : String

  /--
  The proof that it's a valid header name.
  -/
  isValidHeaderValue : IsValidHeaderName value := by decide

  /--
  The proof that we stored the header name in stored as a lower case string.
  -/
  isLowerCase : IsLowerCase value := by decide
deriving Repr, DecidableEq

namespace Name

instance : BEq Name where
  beq a b := a.value = b.value

instance : Hashable Name where
  hash x := Hashable.hash x.value

theorem beq_eq {x y : Name} : (x == y) = (x.value == y.value) :=
  rfl

set_option linter.extra.dupNamespace false in
@[deprecated Header.Name.beq_eq (since := "2026-06-04")]
theorem Name.beq_eq {x y : Name} : (x == y) = (x.value == y.value) :=
  Header.Name.beq_eq

instance : LawfulBEq Name where
  rfl {x} := by simp [beq_eq]
  eq_of_beq {x y} := by grind [beq_eq, Name.ext]

instance : LawfulHashable Name := inferInstance

instance : Inhabited Name where
  default := ⟨"_", by decide, by decide⟩

/--
Attempts to create a `Name` from a `String`, returning `none` if the string contains invalid
characters for HTTP header names or is empty.
-/
def ofString? (s : String) : Option Name :=
  let val := if isAsciiTrimmed s && hasNoUpper s then s else s.trimAscii.toString.toLower
  if h : IsValidHeaderName val ∧ IsLowerCase val then
    some ⟨val, h.left, h.right⟩
  else
    none

/--
Creates a `Name` from a string, panicking with an error message if the string contains invalid
characters for HTTP header names or is empty.
-/
def ofString! (s : String) : Name :=
  match ofString? s with
  | some res => res
  | none => panic! s!"invalid header name: {s.quote}"

/--
Title-cases a lowercase header name.
-/
private def toCanonicalSlow (value : String) : String :=
  let it := value.split '-'
    |>.map (·.copy.capitalize)

  it.intercalateString "-"

/--
Performs a case-insensitive comparison between a `Name` and a `String`. Returns `true` if they match.
-/
@[expose]
def is (name : Name) (s : String) : Bool :=
  name.value == s.toLower


/--
Standard Content-Type header name
-/
def contentType : Header.Name := .mk "content-type"

/--
Standard Content-Length header name
-/
def contentLength : Header.Name := .mk "content-length"

/--
Standard Host header name
-/
def host : Header.Name := .mk "host"

/--
Standard Authorization header name
-/
def authorization : Header.Name := .mk "authorization"

/--
Standard User-Agent header name
-/
def userAgent : Header.Name := .mk "user-agent"

/--
Standard Accept header name
-/
def accept : Header.Name := .mk "accept"

/--
Standard Connection header name
-/
def connection : Header.Name := .mk "connection"

/--
Standard Transfer-Encoding header name
-/
def transferEncoding : Header.Name := .mk "transfer-encoding"

/--
Standard Server header name
-/
def server : Header.Name := .mk "server"

/--
Standard Date header name
-/
def date : Header.Name := .mk "date"

/--
Standard Expect header name
-/
def expect : Header.Name := .mk "expect"

/--
Standard Cookie header name (client → server)
-/
def cookie : Header.Name := .mk "cookie"

/--
Standard Set-Cookie header name (server → client)
-/
def setCookie : Header.Name := .mk "set-cookie"

/--
Standard Location header name
-/
def location : Header.Name := .mk "location"

/--
Standard Proxy-Authorization header name
-/
def proxyAuthorization : Header.Name := .mk "proxy-authorization"

/--
Standard Content-Encoding header name
-/
def contentEncoding : Header.Name := .mk "content-encoding"

/--
Standard Content-Language header name
-/
def contentLanguage : Header.Name := .mk "content-language"

/--
Standard Content-Location header name
-/
def contentLocation : Header.Name := .mk "content-location"

/--
Standard Last-Modified header name
-/
def lastModified : Header.Name := .mk "last-modified"

/--
Standard Referer header name
-/
def referer : Header.Name := .mk "referer"

/--
Standard Origin header name
-/
def origin : Header.Name := .mk "origin"

/--
Standard Keep-Alive header name
-/
def keepAlive : Header.Name := .mk "keep-alive"

/--
Standard If-None-Match header name
-/
def ifNoneMatch : Header.Name := .mk "if-none-match"

/--
Standard If-Modified-Since header name
-/
def ifModifiedSince : Header.Name := .mk "if-modified-since"

private def acceptEncoding : Header.Name := .mk "accept-encoding"
private def acceptLanguage : Header.Name := .mk "accept-language"
private def cacheControl : Header.Name := .mk "cache-control"
private def upgrade : Header.Name := .mk "upgrade"
private def te : Header.Name := .mk "te"
private def pragma : Header.Name := .mk "pragma"
private def xForwardedFor : Header.Name := .mk "x-forwarded-for"

/--
Checks whether the bytes of `arr` starting at `start` spell the lowercase string `s`, ignoring ASCII
case.
-/
private def bytesEqLower (arr : ByteArray) (start : Nat) (s : String) : Bool :=
  go 0
where
  go (i : Nat) : Bool :=
    if h : i < s.utf8ByteSize then
      if h₁ : start + i < arr.size then
        arr[start + i].toAsciiLower == s.getUTF8Byte ⟨i⟩ h && go (i + 1)
      else
        false
    else
      true
  termination_by s.utf8ByteSize - i

/--
Returns the shared constant for a common header name spelled by `arr[start, stop)`, ignoring ASCII
case, so that parsing it allocates nothing.
-/
private def ofKnownBytes? (arr : ByteArray) (start stop : Nat) : Option Name :=
  let check (n : Name) : Option Name :=
    if bytesEqLower arr start n.value then some n else none
  match stop - start with
  | 2 => check te
  | 4 => check host <|> check date
  | 6 => check accept <|> check cookie <|> check expect <|> check origin <|> check pragma
  | 7 => check upgrade <|> check referer
  | 10 => check connection <|> check userAgent <|> check keepAlive
  | 12 => check contentType
  | 13 => check authorization <|> check cacheControl
  | 14 => check contentLength
  | 15 => check acceptEncoding <|> check acceptLanguage <|> check xForwardedFor
  | 17 => check transferEncoding
  | 19 => check proxyAuthorization
  | _ => none

/--
Creates a `Name` from the bytes `arr[start, stop)`, lowercasing ASCII letters. Returns `none` if the
bytes do not form a valid header name. Agrees with `ofString?` on the UTF-8 string of those bytes
when they are a token.
-/
def ofBytes? (arr : ByteArray) (start stop : Nat) : Option Name :=
  match ofKnownBytes? arr start stop with
  | some n => some n
  | none =>
    let bytes := Id.run do
      let mut bytes := arr.extract start stop
      for i in [0:bytes.size] do
        bytes := bytes.set! i (bytes.get! i).toAsciiLower
      return bytes
    match String.fromUTF8? bytes with
    | none => none
    | some val =>
      if h : IsValidHeaderName val ∧ IsLowerCase val then
        some ⟨val, h.left, h.right⟩
      else
        none

private def canonHost : String := toCanonicalSlow "host"
private def canonDate : String := toCanonicalSlow "date"
private def canonServer : String := toCanonicalSlow "server"
private def canonConnection : String := toCanonicalSlow "connection"
private def canonContentType : String := toCanonicalSlow "content-type"
private def canonContentLength : String := toCanonicalSlow "content-length"
private def canonTransferEncoding : String := toCanonicalSlow "transfer-encoding"
private def canonKeepAlive : String := toCanonicalSlow "keep-alive"
private def canonLocation : String := toCanonicalSlow "location"
private def canonSetCookie : String := toCanonicalSlow "set-cookie"

/--
Converts the header name to title case (e.g., "Content-Type").

Note: some well-known headers have unconventional casing (e.g., "WWW-Authenticate"),
but since HTTP header names are case-insensitive, this always uses simple capitalization.
-/
def toCanonical (name : Name) : String :=
  let v := name.value
  match v.utf8ByteSize with
  | 4 => if v == host.value then canonHost else if v == date.value then canonDate else toCanonicalSlow v
  | 6 => if v == server.value then canonServer else toCanonicalSlow v
  | 8 => if v == location.value then canonLocation else toCanonicalSlow v
  | 10 =>
    if v == connection.value then canonConnection
    else if v == keepAlive.value then canonKeepAlive
    else if v == setCookie.value then canonSetCookie
    else toCanonicalSlow v
  | 12 => if v == contentType.value then canonContentType else toCanonicalSlow v
  | 14 => if v == contentLength.value then canonContentLength else toCanonicalSlow v
  | 17 => if v == transferEncoding.value then canonTransferEncoding else toCanonicalSlow v
  | _ => toCanonicalSlow v

instance : ToString Name where
  toString name := name.toCanonical

end Std.Http.Header.Name
