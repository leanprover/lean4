/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time
public import Std.Http.Data.URI
import Init.Data.String.Search
import Init.Data.String.TakeDrop

public section

/-!
# Cookies

This module implements the user-agent side of RFC 6265: the `Set-Cookie` parser (§5.2), the
cookie-date parser (§5.1.1), and domain and path matching (§5.1.3, §5.1.4). `Cookie.Store` and
`Cookie.Jar` (`Std.Http.Data.Cookie.Jar`) build the storage model and the `Cookie` header on them.

A user agent parses `Set-Cookie` leniently: the grammar of §4.1 is what servers should send, not
what a client may refuse. A name or a value may hold any character but `;`, and a malformed
attribute is ignored rather than failing the cookie.

Reference: https://www.rfc-editor.org/rfc/rfc6265
-/

namespace Std.Http

set_option linter.all true

open Std.Time Std.Time.Internal

/--
A cookie as the store keeps it (RFC 6265 §5.3).
-/
structure Cookie where
  /--
  The cookie name.
  -/
  name : String

  /--
  The cookie value.
  -/
  value : String

  /--
  The canonicalized host that set the cookie when `hostOnly`, otherwise the `Domain` attribute,
  lowercase and without a leading `.`.
  -/
  domain : String

  /--
  The path the cookie applies to and below: the `Path` attribute, or the default path of the
  request that set it.
  -/
  path : String

  /--
  When the cookie expires; `none` for a session cookie, which lives as long as its store.
  -/
  expiry : Option Timestamp

  /--
  When the cookie was first stored. A replacement keeps the time of the cookie it replaces.
  -/
  creation : Timestamp

  /--
  When the cookie was last stored or sent.
  -/
  lastAccess : Timestamp

  /--
  Whether the cookie goes only to the host in `domain`, not to its subdomains.
  -/
  hostOnly : Bool

  /--
  Whether the cookie goes only over a secure channel (`https`).
  -/
  secure : Bool

  /--
  Whether the cookie is only for HTTP requests. Everything this library sends is one, so the flag
  is kept but changes nothing here.
  -/
  httpOnly : Bool
deriving Repr, BEq

namespace Cookie

/--
A parsed `Set-Cookie` header (RFC 6265 §5.2), before the store interprets it. Each attribute holds
its last valid occurrence; malformed ones are ignored.
-/
structure SetCookie where
  /--
  The cookie name, trimmed and not empty.
  -/
  name : String

  /--
  The cookie value, trimmed; may be empty.
  -/
  value : String

  /--
  The `Expires` attribute, when it is a valid cookie-date.
  -/
  expires : Option Timestamp := none

  /--
  The `Max-Age` attribute in seconds. A value of zero or less deletes the cookie.
  -/
  maxAge : Option Second.Offset := none

  /--
  The `Domain` attribute, lowercase and without a leading `.`.
  -/
  domain : Option String := none

  /--
  The `Path` attribute; `none` when absent or not starting with `/`, which selects the default
  path.
  -/
  path : Option String := none

  /--
  Whether the `Secure` attribute is present.
  -/
  secure : Bool := false

  /--
  Whether the `HttpOnly` attribute is present.
  -/
  httpOnly : Bool := false
deriving Repr, BEq

/-! ## Dates (RFC 6265 §5.1.1) -/

/-- `delimiter = %x09 / %x20-2F / %x3B-40 / %x5B-60 / %x7B-7E` -/
@[inline] private def isDateDelimiter (b : UInt8) : Bool :=
  b == 0x09 || (0x20 ≤ b && b ≤ 0x2F) || (0x3B ≤ b && b ≤ 0x40) || (0x5B ≤ b && b ≤ 0x60) ||
    (0x7B ≤ b && b ≤ 0x7E)

/-- The tokens of a date: the runs of non-delimiter bytes. -/
private def dateTokens (s : String) : List (List UInt8) :=
  let (tokens, last) := s.toUTF8.foldl (init := ([], [])) fun (tokens, token) b =>
    if isDateDelimiter b then
      (if token.isEmpty then tokens else token.reverse :: tokens, [])
    else (tokens, b :: token)
  (if last.isEmpty then tokens else last.reverse :: tokens).reverse

/-- Takes at most `max` leading digits: their count, their value and the rest. -/
private def takeDigits (bytes : List UInt8) (max : Nat) : Nat × Nat × List UInt8 :=
  go bytes max 0 0
where
  go : List UInt8 → Nat → Nat → Nat → Nat × Nat × List UInt8
    | b :: rest, k + 1, count, value =>
      if Internal.Char.isDigitByte b then
        go rest k (count + 1) (value * 10 + (b - '0'.toUInt8).toNat)
      else (count, value, b :: rest)
    | rest, _, count, value => (count, value, rest)

/-- Whether what follows a number lets it end there: nothing, or a non-digit. -/
@[inline] private def endsNumber : List UInt8 → Bool
  | [] => true
  | b :: _ => !Internal.Char.isDigitByte b

/-- `digits = min*maxDIGIT ( non-digit *OCTET )`, giving the value. -/
private def number? (bytes : List UInt8) (min max : Nat) : Option Nat :=
  let (count, value, rest) := takeDigits bytes max
  if min ≤ count && endsNumber rest then some value else none

/-- `time = hms-time ( non-digit *OCTET )`, `hms-time = time-field ":" time-field ":" time-field`. -/
private def time? (bytes : List UInt8) : Option PlainTime := do
  let field (bytes : List UInt8) : Option (Nat × List UInt8) :=
    let (count, value, rest) := takeDigits bytes 2
    if count ≥ 1 then some (value, rest) else none
  let colon (bytes : List UInt8) : Option (List UInt8) :=
    match bytes with
    | b :: rest => if b == ':'.toUInt8 then some rest else none
    | [] => none
  let (hour, rest) ← field bytes
  let (minute, rest) ← field (← colon rest)
  let (second, rest) ← field (← colon rest)
  guard (endsNumber rest)
  -- A cookie-date has no leap second, which `Second.Ordinal true` would admit.
  let second : Second.Ordinal false ← Bounded.LE.ofNat? second
  return .ofHourMinuteSeconds (← Bounded.LE.ofNat? hour) (← Bounded.LE.ofNat? minute)
    (second.expandTop (by decide))

/-- `day-of-month = 1*2DIGIT ( non-digit *OCTET )`. -/
private def day? (bytes : List UInt8) : Option Day.Ordinal := do
  Bounded.ofInt? (← number? bytes 1 2)

/-- `month = ( "jan" / "feb" / … / "dec" ) *OCTET`, case-insensitively. -/
private def month? (bytes : List UInt8) : Option Month.Ordinal :=
  match bytes with
  | a :: b :: c :: _ =>
    let lead := String.ofList ([a, b, c].map fun b => (Char.ofUInt8 b).toLower)
    (parseMonthShort .enUS).run lead.capitalize |>.toOption
  | _ => none

/-- `year = 2*4DIGIT ( non-digit *OCTET )`; a two-digit year 70–99 is 19xx and 00–69 is 20xx. -/
private def year? (bytes : List UInt8) : Option Year.Offset := do
  let year ← number? bytes 2 4
  let year := if 70 ≤ year && year ≤ 99 then year + 1900 else if year ≤ 69 then year + 2000 else year
  return .ofNat year

/-- The fields of a date found so far by `parseDate`. -/
private structure DateFields where
  time : Option PlainTime := none
  day : Option Day.Ordinal := none
  month : Option Month.Ordinal := none
  year : Option Year.Offset := none

/-- Gives `token` to the first field that is still missing and that it reads as. -/
private def DateFields.add (fields : DateFields) (token : List UInt8) : DateFields := Id.run do
  if fields.time.isNone then
    if let some time := time? token then return { fields with time := some time }
  if fields.day.isNone then
    if let some day := day? token then return { fields with day := some day }
  if fields.month.isNone then
    if let some month := month? token then return { fields with month := some month }
  if fields.year.isNone then
    if let some year := year? token then return { fields with year := some year }
  return fields

/--
Parses a cookie-date with the algorithm of RFC 6265 §5.1.1, which accepts the date formats servers
send in `Expires` (IMF-fixdate, RFC 850 and asctime among them). The first token that reads as a
valid time is the time, then the first that reads as a valid day, month and year. `none` when a
field is missing, the year is before 1601, or the date does not exist.
-/
def parseDate (s : String) : Option Timestamp := do
  let fields := (dateTokens s).foldl DateFields.add {}
  let year ← fields.year
  guard (1601 ≤ year)
  let date ← PlainDate.ofYearMonthDay? year (← fields.month) (← fields.day)
  return (PlainDateTime.mk date (← fields.time)).toTimestampWithZone .UTC

/-! ## The `Set-Cookie` header (RFC 6265 §5.2) -/

/-- The parts of `s` between occurrences of `c`. -/
private def splitAt (s : String) (c : Char) : List String :=
  let (parts, last) := s.foldl (init := ([], "")) fun (parts, part) ch =>
    if ch == c then (part :: parts, "") else (parts, part.push ch)
  (last :: parts).reverse

/-- Splits at the first `=`: the part before it and the part after it, or `none` without one. -/
private def splitAtEquals (s : String) : Option (String × String) :=
  match s.toList.span (· != '=') with
  | (name, _ :: value) => some (String.ofList name, String.ofList value)
  | (_, []) => none

/-- `Max-Age`: a DIGIT or `-`, then DIGITs only (RFC 6265 §5.2.2). -/
private def maxAge? (value : String) : Option Second.Offset :=
  let (negative, digits) :=
    if value.startsWith "-" then (true, (value.drop 1).toString) else (false, value)
  if !digits.isEmpty && digits.all Char.isDigit then
    let n : Int := digits.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0
    some (.ofInt (if negative then -n else n))
  else none

/-- Applies one `cookie-av` to the cookie: the last valid occurrence of each attribute wins. -/
private def applyAttribute (cookie : SetCookie) (av : String) : SetCookie :=
  let (name, value) := (splitAtEquals av).getD (av, "")
  let value := value.trimAscii.toString
  match name.trimAscii.toString.toLower with
  | "expires" => match parseDate value with
    | some t => { cookie with expires := some t }
    | none => cookie
  | "max-age" => match maxAge? value with
    | some n => { cookie with maxAge := some n }
    | none => cookie
  | "domain" =>
    -- RFC 6265 §5.2.3: an empty value is ignored; a leading `.` is dropped.
    if value.isEmpty then cookie
    else
      let domain := if value.startsWith "." then (value.drop 1).toString else value
      { cookie with domain := some domain.toLower }
  | "path" =>
    -- RFC 6265 §5.2.4: a value that is empty or does not start with `/` selects the default path.
    { cookie with path := if value.startsWith "/" then some value else none }
  | "secure" => { cookie with secure := true }
  | "httponly" => { cookie with httpOnly := true }
  | _ => cookie

/--
Parses a `Set-Cookie` header value with the user-agent algorithm of RFC 6265 §5.2. The name and
value are what comes before and after the first `=` of the text before the first `;`, trimmed.
`none` when that text has no `=` or the name is empty, in which case the header is ignored.
-/
def parseSetCookie (header : String) : Option SetCookie := do
  let pair :: attributes := splitAt header ';' | none
  let (name, value) ← splitAtEquals pair
  let name := name.trimAscii.toString
  guard !name.isEmpty
  return attributes.foldl applyAttribute { name, value := value.trimAscii.toString }

/-! ## Matching (RFC 6265 §5.1.3, §5.1.4) -/

/--
Whether `host` domain-matches `domain` (RFC 6265 §5.1.3): they are identical, or `host` is a name
(not an IP address) that ends with `.` followed by `domain`.
-/
def domainMatch (host : URI.Host) (domain : String) : Bool :=
  let name := toString host
  name == domain ||
    (host matches .name _) && !domain.isEmpty && name.endsWith ("." ++ domain)

/--
The default path of a request path (RFC 6265 §5.1.4): `/` when the path is empty, does not start
with `/` or has no other `/`; otherwise the path up to, and not including, its last `/`.
-/
def defaultPath (path : String) : String :=
  if !path.startsWith "/" then "/"
  else
    match String.ofList ((path.toList.reverse.dropWhile (· != '/')).drop 1).reverse with
    | "" => "/"
    | directory => directory

/--
Whether `requestPath` path-matches `cookiePath` (RFC 6265 §5.1.4): they are identical, or
`cookiePath` is a prefix of `requestPath` that ends with `/` or is followed by `/` there.
-/
def pathMatch (requestPath cookiePath : String) : Bool :=
  requestPath == cookiePath ||
    requestPath.startsWith cookiePath &&
      (cookiePath.endsWith "/" ||
        requestPath.toUTF8[cookiePath.utf8ByteSize]? == some '/'.toUInt8)

end Std.Http.Cookie
