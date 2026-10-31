import Std.Http
import Std.Http.Protocol.H1.Parser

open Std Internal Parsec ByteArray
open Std.Http.Protocol.H1

private def ensure (name : String) (cond : Bool) (msg : String) : IO Unit := do
  unless cond do
    throw <| IO.userError s!"{name}: {msg}"

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

#eval show IO Unit from do
  let methods : Array String := #["GET", "POST", "PUT", "PATCH", "DELETE", "OPTIONS", "HEAD", "CONNECT"]
  let targets : Array String := #["/", "/a", "/a/b", "/a/b?q=1", "*", "http://example.com", "example.com:443"]
  let versions : Array String := #["HTTP/1.1", "HTTP/1.0"]

  let mut gen : StdGen := StdGen.mk 0x5eed1234 0x12345
  for i in [0:400] do
    let (m, g1) := pick! gen methods
    let (t, g2) := pick! g1 targets
    let (v, g3) := pick! g2 versions
    gen := g3

    let line := s!"{m} {t} {v}\r\n"
    expectRequestOk line

    -- Mutation 1: drop the first space
    expectRequestFail s!"{m}{t} {v}\r\n"

    -- Mutation 2: invalid version token
    expectRequestFail s!"{m} {t} HTTP/2.0\r\n"

    -- Mutation 3: bad method character
    expectRequestFail s!"{m}! {t} {v}\r\n"

    ensure "request fuzz progress" (i < 100000) "unreachable safety check"

#eval show IO Unit from do
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
    expectStatusFail s!"HTTP/1.1 {pad3 code} bad{Char.ofNat 127}\r\n"

#eval show IO Unit from do
  -- Randomized malformed gibberish smoke: parser must simply return error or success,
  -- but never crash/panic.
  let mut gen : StdGen := StdGen.mk 0x31415926 0x27182818
  for _ in [0:300] do
    let (len, g1) := randBelow gen 80
    let (tok, g2) := randomToken g1 (len + 1)
    gen := g2
    let _ := runParser (parseRequestLine {}) (tok ++ "\r\n")
    let _ := runParser (parseStatusLine {}) (tok ++ "\r\n")
  pure ()

-- Component tests for individual parser parts.
#eval show IO Unit from do
  -- parseSingleHeader
  let sh1 ← expectOk "parseSingleHeader some" (parseSingleHeader {} <* eof) "Host: x\r\n"
  ensure "parseSingleHeader some present" sh1.isSome "expected some header"

  let sh2 ← expectOk "parseSingleHeader none" (parseSingleHeader {} <* eof) "\r\n"
  ensure "parseSingleHeader none present" sh2.isNone "expected header terminator"

  -- parseChunkSize / parseChunkPartial
  let (n1, ext1) ← expectOk "parseChunkSize bare" (parseChunkSize {} <* eof) "A\r\n"
  ensure "parseChunkSize value" (n1 == 10) "chunk-size mismatch"
  ensure "parseChunkSize ext empty" (ext1.isEmpty) "expected no extensions"

  let (n2, ext2) ← expectOk "parseChunkSize ext" (parseChunkSize {} <* eof) "4;foo=bar;baz=\"qux\"\r\n"
  ensure "parseChunkSize ext value" (n2 == 4) "chunk-size mismatch with ext"
  ensure "parseChunkSize ext count" (ext2.size == 2) "expected 2 extensions"

  let cp1 ← expectOk "parseChunkPartial some" (parseChunkPartial {} <* eof) "4\r\nWiki"
  ensure "parseChunkPartial some isSome" cp1.isSome "expected chunk data"
  ensure "parseChunkPartial some size" ((cp1.map (fun (n, _, _) => n)).getD 0 == 4) "size mismatch"

  let cp0 ← expectOk "parseChunkPartial none" (parseChunkPartial {} <* eof) "0\r\n"
  ensure "parseChunkPartial none isNone" cp0.isNone "expected last-chunk marker"

  -- parseFixedSizeData / parseChunkSizedData
  let fs1 ← expectOk "parseFixedSizeData complete" (parseFixedSizeData 4 <* eof) "Wiki"
  ensure "parseFixedSizeData complete shape"
    (match fs1 with | .complete _ => true | _ => false)
    "expected complete result"
  let fs2 ← expectOk "parseFixedSizeData incomplete" (parseFixedSizeData 4 <* eof) "Wi"
  ensure "parseFixedSizeData incomplete shape"
    (match fs2 with | .incomplete _ 2 => true | _ => false)
    "expected incomplete result with remaining=2"

  let cs1 ← expectOk "parseChunkSizedData complete" (parseChunkSizedData 4 <* eof) "Wiki\r\n"
  ensure "parseChunkSizedData complete shape"
    (match cs1 with | .complete _ => true | _ => false)
    "expected complete chunk-sized result"
  let cs2 ← expectOk "parseChunkSizedData incomplete" (parseChunkSizedData 4 <* eof) "Wi"
  ensure "parseChunkSizedData incomplete shape"
    (match cs2 with | .incomplete _ 2 => true | _ => false)
    "expected incomplete chunk-sized result with remaining=2"

  -- parseTrailers
  let trailers ← expectOk "parseTrailers ok" (parseTrailers {} <* eof) "X-Test: a\r\nY-Test: b\r\n\r\n"
  ensure "parseTrailers count" (trailers.size == 2) "expected 2 trailers"
  expectFail "parseTrailers forbidden" (parseTrailers {} <* eof) "Content-Length: 1\r\n\r\n"

  -- parseRequestLineRawVersion / parseStatusLineRawVersion
  let (m1, _, v1) ← expectOk "parseRequestLineRawVersion" (parseRequestLineRawVersion {} <* eof) "GET / HTTP/1.1\r\n"
  ensure "parseRequestLineRawVersion method" (m1 == Std.Http.Method.get) "method mismatch"
  ensure "parseRequestLineRawVersion version" (v1 == some Std.Http.Version.v11) "expected recognized v11"
  let (_, rv) ← expectOk "parseStatusLineRawVersion" (parseStatusLineRawVersion {} <* eof) "HTTP/1.1 204 No Content\r\n"
  ensure "parseStatusLineRawVersion recognized" (rv == some Std.Http.Version.v11) "expected v11"

  -- parseRequestLine / parseStatusLine failures
  expectFail "parseRequestLine invalid version" (parseRequestLine {} <* eof) "GET / HTTP/2.0\r\n"
  expectFail "parseStatusLine invalid version" (parseStatusLine {} <* eof) "HTTP/2.0 200 OK\r\n"
