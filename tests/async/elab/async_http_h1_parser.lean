module

import Std.Http.Test.Helpers
import Std.Http.Protocol.H1.Parser

/-!
# HTTP/1.1 parser units

The `Std.Http.Protocol.H1` Parsec parsers on their own: request and status lines, field lines, chunk
sizes, chunk data and trailers, and lines of arbitrary tokens. RFC 9112 §3, §4, §5, §7.1.
-/

open Std Internal Parsec ByteArray
open Std.Http.Protocol.H1
open Std.Http.Internal.Test

private def runParser (p : Parser α) (s : String) : Except String α :=
  match (p <* eof).run s.toUTF8 with
  | .ok x => .ok x
  | .error e => .error e

private def randBelow (gen : StdGen) (maxExclusive : Nat) : Nat × StdGen :=
  if maxExclusive = 0 then
    (0, gen)
  else
    randNat gen 0 (maxExclusive - 1)

private def pick! [Inhabited α] (gen : StdGen) (xs : Array α) : α × StdGen :=
  let (i, gen') := randBelow gen xs.size
  (xs[i]!, gen')

private def randomToken (gen : StdGen) (len : Nat) : String × StdGen := Id.run do
  let mut g := gen
  let mut out := ""
  for _ in [0:len] do
    let (r, g') := randBelow g 38
    g := g'
    let c :=
      if r < 26 then Char.ofNat (97 + r)
      else if r < 36 then Char.ofNat (48 + (r - 26))
      else if r = 36 then '-'
      else '_'
    out := out.push c
  (out, g)

private def randomReason (gen : StdGen) (len : Nat) : String × StdGen := Id.run do
  let mut g := gen
  let mut out := ""
  for _ in [0:len] do
    let (r, g') := randBelow g 30
    g := g'
    let c := if r < 26 then Char.ofNat (65 + r) else ' '
    out := out.push c
  (out.trimAscii.toString, g)

private def pad3 (n : Nat) : String :=
  if n < 10 then s!"00{n}" else if n < 100 then s!"0{n}" else s!"{n}"

private def expectRequestOk (s : String) : IO Unit := do
  match runParser (parseRequestLine {}) s with
  | .ok _ => pure ()
  | .error e => throw <| IO.userError s!"expected request-line success for {s.quote}, got: {e}"

private def expectRequestFail (s : String) : IO Unit := do
  match runParser (parseRequestLine {}) s with
  | .ok _ => throw <| IO.userError s!"expected request-line failure for {s.quote}"
  | .error _ => pure ()

private def expectStatusOk (s : String) : IO Unit := do
  match runParser (parseStatusLine {}) s with
  | .ok _ => pure ()
  | .error e => throw <| IO.userError s!"expected status-line success for {s.quote}, got: {e}"

private def expectStatusFail (s : String) : IO Unit := do
  match runParser (parseStatusLine {}) s with
  | .ok _ => throw <| IO.userError s!"expected status-line failure for {s.quote}"
  | .error _ => pure ()

private def expectOk {α} (name : String) (p : Parser α) (s : String) : IO α := do
  match runParser p s with
  | .ok x => pure x
  | .error e => throw <| IO.userError s!"{name}: expected success for {s.quote}, got {e}"

private def expectFail {α} (name : String) (p : Parser α) (s : String) : IO Unit := do
  match runParser p s with
  | .ok _ => throw <| IO.userError s!"{name}: expected failure for {s.quote}"
  | .error _ => pure ()

/-! ## Request and status lines (RFC 9112 §3, §4) -/

#eval checkCases "Generated request and status lines" #[
    ("request lines from 8 methods × 7 targets × 2 versions, and their mutations", do
      let methods : Array String := #["GET", "POST", "PUT", "PATCH", "DELETE", "OPTIONS", "HEAD", "CONNECT"]
      let targets : Array String := #["/", "/a", "/a/b", "/a/b?q=1", "*", "http://example.com", "example.com:443"]
      let versions : Array String := #["HTTP/1.1", "HTTP/1.0"]
      for m in methods do
        for t in targets do
          for v in versions do
            expectRequestOk s!"{m} {t} {v}\r\n"
            -- Mutation 1: drop the first space
            expectRequestFail s!"{m}{t} {v}\r\n"
            -- Mutation 2: invalid version token
            expectRequestFail s!"{m} {t} HTTP/2.0\r\n"
            -- Mutation 3: bad method character
            expectRequestFail s!"{m}! {t} {v}\r\n"),
    ("status lines with known codes and generated reasons, and their mutations", do
      let knownCodes : Array Nat := #[200, 201, 204, 301, 400, 404, 500, 503]
      let mut gen : StdGen := StdGen.mk 0xabcde123 0x777
      for _ in [0:400] do
        let (code, g1) := pick! gen knownCodes
        let (len, g2) := randBelow g1 20
        let (reasonRaw, g3) := randomReason g2 (len + 1)
        gen := g3
        let reason := if reasonRaw.isEmpty then "OK" else reasonRaw
        let line := s!"HTTP/1.1 {pad3 code} {reason}\r\n"
        expectStatusOk line
        -- Mutation 1: unsupported version
        expectStatusFail s!"HTTP/2.0 {pad3 code} {reason}\r\n"
        -- Mutation 2: non-digit in status code
        expectStatusFail s!"HTTP/1.1 A{(pad3 code).drop 1} {reason}\r\n"
        -- Mutation 3: illegal reason byte (DEL)
        expectStatusFail s!"HTTP/1.1 {pad3 code} bad{Char.ofNat 127}\r\n")
  ] (·.2)

#eval checkCases "Raw-version parsers" #[
    ("parseRequestLineRawVersion", do
      let (m1, _, v1) ← expectOk "parseRequestLineRawVersion" (parseRequestLineRawVersion {} <* eof) "GET / HTTP/1.1\r\n"
      ensure (m1 == Std.Http.Method.get) "parseRequestLineRawVersion method: method mismatch"
      ensure (v1 == some Std.Http.Version.v11) "parseRequestLineRawVersion version: expected recognized v11"),
    ("parseStatusLineRawVersion", do
      let (_, rv) ← expectOk "parseStatusLineRawVersion" (parseStatusLineRawVersion {} <* eof) "HTTP/1.1 204 No Content\r\n"
      ensure (rv == some Std.Http.Version.v11) "parseStatusLineRawVersion recognized: expected v11")
  ] (·.2)

/-! ## Field lines (RFC 9112 §5) -/

#eval checkCases "parseSingleHeader" #[
    ("parseSingleHeader some", do
      let sh1 ← expectOk "parseSingleHeader some" (parseSingleHeader {} <* eof) "Host: x\r\n"
      ensure sh1.isSome "parseSingleHeader some present: expected some header"),
    ("parseSingleHeader none", do
      let sh2 ← expectOk "parseSingleHeader none" (parseSingleHeader {} <* eof) "\r\n"
      ensure sh2.isNone "parseSingleHeader none present: expected header terminator")
  ] (·.2)

/-! ## Chunks and trailers (RFC 9112 §7.1) -/

-- A chunk-size line cut inside an extension must report `.eof` so the machine waits for more data.
#eval checkCases "truncated chunk-size line" #[
    "5", "5;", "5 ", "5;a", "5;a=", "5;a=b", "5;a=\"b"
  ] fun input => match parseChunkSize {} input.toUTF8.iter with
    | .error _ .eof => pure ()
    | _ => throw <| IO.userError s!"expected .eof for truncated chunk-size line {input.quote}"

#eval checkCases "Component tests for individual parser parts" #[
    ("parseChunkSize bare", do
      let (n1, ext1) ← expectOk "parseChunkSize bare" (parseChunkSize {} <* eof) "A\r\n"
      ensure (n1 == 10) "parseChunkSize value: chunk-size mismatch"
      ensure ext1.isEmpty "parseChunkSize ext empty: expected no extensions"),
    ("parseChunkSize ext", do
      let (n2, ext2) ← expectOk "parseChunkSize ext" (parseChunkSize {} <* eof) "4;foo=bar;baz=\"qux\"\r\n"
      ensure (n2 == 4) "parseChunkSize ext value: chunk-size mismatch with ext"
      ensure (ext2.size == 2) "parseChunkSize ext count: expected 2 extensions"),
    ("parseChunkPartial some", do
      let cp1 ← expectOk "parseChunkPartial some" (parseChunkPartial {} <* eof) "4\r\nWiki"
      ensure cp1.isSome "parseChunkPartial some isSome: expected chunk data"
      ensure ((cp1.map (fun (n, _, _) => n)).getD 0 == 4) "parseChunkPartial some size: size mismatch"),
    ("parseChunkPartial none", do
      let cp0 ← expectOk "parseChunkPartial none" (parseChunkPartial {} <* eof) "0\r\n"
      ensure cp0.isNone "parseChunkPartial none isNone: expected last-chunk marker"),
    ("parseFixedSizeData complete", do
      let fs1 ← expectOk "parseFixedSizeData complete" (parseFixedSizeData 4 <* eof) "Wiki"
      ensure (match fs1 with | .complete _ => true | _ => false) "parseFixedSizeData complete shape: expected complete result"),
    ("parseFixedSizeData incomplete", do
      let fs2 ← expectOk "parseFixedSizeData incomplete" (parseFixedSizeData 4 <* eof) "Wi"
      ensure (match fs2 with | .incomplete _ 2 => true | _ => false)
        "parseFixedSizeData incomplete shape: expected incomplete result with remaining=2"),
    ("parseChunkSizedData complete", do
      let cs1 ← expectOk "parseChunkSizedData complete" (parseChunkSizedData 4 <* eof) "Wiki\r\n"
      ensure (match cs1 with | .complete _ => true | _ => false)
        "parseChunkSizedData complete shape: expected complete chunk-sized result"),
    ("parseChunkSizedData incomplete", do
      let cs2 ← expectOk "parseChunkSizedData incomplete" (parseChunkSizedData 4 <* eof) "Wi"
      ensure (match cs2 with | .incomplete _ 2 => true | _ => false)
        "parseChunkSizedData incomplete shape: expected incomplete chunk-sized result with remaining=2"),
    ("parseTrailers ok", do
      let trailers ← expectOk "parseTrailers ok" (parseTrailers {} <* eof) "X-Test: a\r\nY-Test: b\r\n\r\n"
      ensure (trailers.size == 2) "parseTrailers count: expected 2 trailers"),
    ("parseTrailers forbidden", expectFail "parseTrailers forbidden" (parseTrailers {} <* eof)
      "Content-Length: 1\r\n\r\n")
  ] (·.2)

/-! ## Arbitrary lines -/

#eval checkCases "Lines with no version token" #[
    -- A line of token characters has no SP and no version, so neither parser accepts it.
    ("300 token lines through both parsers", do
      let mut gen : StdGen := StdGen.mk 0x31415926 0x27182818
      for _ in [0:300] do
        let (len, g1) := randBelow gen 80
        let (tok, g2) := randomToken g1 (len + 1)
        gen := g2
        expectRequestFail (tok ++ "\r\n")
        expectStatusFail (tok ++ "\r\n"))
  ] (·.2)
