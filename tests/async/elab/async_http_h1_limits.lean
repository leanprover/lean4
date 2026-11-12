module

import Std.Http.Test.Helpers
import Std.Http.Test.Machine

/-!
# HTTP/1.1 limits

Every size and count limit a server applies to a request, at its boundary: the start line and
target, header fields, leading empty lines, the body, chunk extensions, trailers and buffered input.
RFC 9112 §2.2, §3, §5, §6.3, §7.1; RFC 9110 §5.4; RFC 6585 §5. Regressions: #16080, #16282.
`maxBodySize` bounds the bytes of a chunked body on the wire, chunk framing included (Std.Http
policy).
-/

open Std Http
open Std.Async
open Std.Http.Protocol.H1
open Std.Http.Internal.Test

private def repeatStr (s : String) (n : Nat) : String := String.join (List.replicate n s)

private def ok200 : Want := .exact okResponse

/-- Serves `raw` with `handler` and `config`; with `closeInput` the client sends EOF after it. -/
private def expectServer (raw : String) (want : Want) (config : Std.Http.Config := testConfig)
    (handler : TestHandler := okHandler) (closeInput : Bool := false) : IO Unit :=
  checkHandler raw handler want config closeInput

/-- Status `200` when `ok`, otherwise `fail`. -/
private def okOr (ok : Bool) (fail : String) : Want :=
  .status (if ok then "HTTP/1.1 200" else fail)

private def readAllOk : TestHandler := fun req => do
  let _body : String ← req.body.readAll
  Response.ok |>.text "ok"

/-! ## Start line and target (RFC 9112 §3) -/

#eval checkCases "Start line and target limits: server" #[
    -- The method and version are bounded, so a line over the limit is over it because of its target.
    ("request-line too long → 414",
      s!"GET /{repeatStr "a" 2000} HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n",
      Want.status "HTTP/1.1 414", { testConfig with maxStartLineLength := 1000 }, okHandler),
    ("URI at maxUriLength limit → 200",
      s!"GET /{"/".intercalate (List.replicate 32 (repeatStr "a" 255))} HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n",
      ok200, { testConfig with maxStartLineLength := 16384 }, okHandler),
    ("URI one byte over limit → 414",
      s!"GET /{"/".intercalate (List.replicate 32 (repeatStr "a" 255))}a HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n",
      .status "HTTP/1.1 414", { testConfig with maxStartLineLength := 16384 }, okHandler),
    ("valid targets under maxUriLength: 257-byte segment", mkGetClose ("/" ++ repeatStr "a" 257), .status "HTTP/1.1 200", testConfig, uriHandler),
    ("valid targets under maxUriLength: 600-byte segment", mkGetClose ("/" ++ repeatStr "a" 600), .status "HTTP/1.1 200", testConfig, uriHandler),
    ("valid targets under maxUriLength: 129 segments", mkGetClose (repeatStr "/a" 129), .status "HTTP/1.1 200", testConfig, uriHandler),
    ("valid targets under maxUriLength: 101 query parameters",
      mkGetClose ("/?" ++ "&".intercalate (List.replicate 101 "a=1")), .status "HTTP/1.1 200", testConfig, uriHandler),
    -- `GET ` and ` HTTP/1.1\r\n` add 15 bytes, so a 8177-byte target makes a 8192-byte line.
    ("8177-byte target", mkGetClose ("/" ++ repeatStr "a" 8176), .status "HTTP/1.1 200", testConfig, uriHandler),
    ("8178-byte target", mkGetClose ("/" ++ repeatStr "a" 8177), .status "HTTP/1.1 414", testConfig, uriHandler),
    ("8192-byte target", mkGetClose ("/" ++ repeatStr "a" 8191), .status "HTTP/1.1 414", testConfig, uriHandler),
    ("8193-byte target", mkGetClose ("/" ++ repeatStr "a" 8192), .status "HTTP/1.1 414", testConfig, uriHandler),
    -- A small `maxUriLength` still answers 414.
    ("400-byte target, maxUriLength 300", mkGetClose ("/" ++ repeatStr "a" 399), .status "HTTP/1.1 414",
      { testConfig with maxUriLength := 300 }, uriHandler)
  ] fun (_, raw, want, config, handler) => expectServer raw want config handler

#eval checkCases "maxStartLineLength = maxUriLength = 64: every path length of 1–58" #[
    ("path lengths 1–58", do
      let limit : Nat := 64
      let config : Std.Http.Config := { testConfig with maxStartLineLength := limit, maxUriLength := limit }
      for pathLen in [1:59] do
        let path := "/" ++ String.ofList (List.replicate (pathLen - 1) 'a')
        let lineLen := 4 + pathLen + 11
        try expectServer s!"GET {path} HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
              (okOr (lineLen ≤ limit) "HTTP/1.1 414") config (closeInput := true)
        catch e => throw <| IO.userError s!"line of {lineLen} bytes: {e}")
  ] (·.2)


private def clientGet : Request.Head :=
  { method := .get, version := .v11, uri := RequestTarget.originForm! "/",
    headers := Headers.empty.insert! "Host" "example.com" }

#eval checkCases "Client: a 64 KiB reason phrase fails" #[
    ("HTTP/1.1 200 <64 KiB>", MachineTester.sending "a 64 KiB reason phrase"
      |>.send clientGet |>.step
      |>.feed s!"HTTP/1.1 200 {repeatStr "r" 65536}\r\nContent-Length: 0\r\n\r\n" |>.step
      |>.assert (·.failed) "expected a start-line or reason-phrase limit failure" |>.run)
  ] (·.2)

/-! ## Header fields (RFC 9110 §5.4, RFC 6585 §5) -/

/-- Feed all bytes at once and run one step. -/
private def runMachine (raw : String) (cfg : Protocol.H1.Config) : Machine .receiving :=
  let machine : Machine .receiving := { config := cfg }
  (machine.feed raw.toUTF8).step.1

#eval checkCases "maxHeaderBytes on the machine" #[
    -- "host" (4) + "example.com" (11) + 4 = 19 bytes for the first field; "x-a" (3) + "somevalue1"
    -- (10) + 4 = 17 bytes for the second, 36 in all.
    ("two fields over a 35-byte limit fail", do
      let m := runMachine "GET / HTTP/1.1\r\nhost: example.com\r\nx-a: somevalue1\r\n\r\n" { maxHeaderBytes := 35 }
      ensure (m.error == some .headersTooLarge) s!"expected headersTooLarge, got {repr m.error}"),
    ("the same request under a 100-byte limit", do
      let machine : Machine .receiving := { config := { maxHeaderBytes := 100 } }
      let (m, step) := (machine.feed "GET / HTTP/1.1\r\nhost: example.com\r\nx-a: somevalue1\r\n\r\n".toUTF8).step
      ensure (!m.failed && step.events.any (· matches .endHeaders _)) s!"expected the head, got {repr step.events}"),
    ("one 19-byte field at a 19-byte limit", ensure
      (!(runMachine "GET / HTTP/1.1\r\nhost: example.com\r\n\r\n" { maxHeaderBytes := 19 }).failed)
      "unexpected failure"),
    ("one 19-byte field at an 18-byte limit", do
      let m := runMachine "GET / HTTP/1.1\r\nhost: example.com\r\n\r\n" { maxHeaderBytes := 18 }
      ensure (m.error == some .headersTooLarge) s!"expected headersTooLarge, got {repr m.error}")
  ] (·.2)

#eval checkCases "Header size limits: server" #[
    ("header name > 256 bytes → 400",
      s!"GET / HTTP/1.1\x0d\nHost: example.com\x0d\n{repeatStr "X" 257}: value\x0d\nConnection: close\x0d\n\x0d\n", Want.exact r400),
    ("header value too long → 400",
      s!"GET / HTTP/1.1\x0d\nHost: example.com\x0d\nX-Long: {repeatStr "x" 9000}\x0d\nConnection: close\x0d\n\x0d\n", .exact r400),
    -- `maxHeaders` is 50 by default, Host and Connection included.
    ("50 header fields → 200",
      "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n" ++
        String.join ((List.range 48).map fun i => s!"X-Header-{i}: value{i}\x0d\n") ++ "\x0d\n", ok200),
    ("too many headers (51) → 431",
      "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n" ++
        String.join ((List.range 49).map fun i => s!"X-Header-{i}: value{i}\x0d\n") ++ "\x0d\n", .exact r431),
    -- 9 fields of 8000 bytes stay under `maxHeaders` and `maxHeaderValueLength`, over `maxHeaderBytes`.
    ("total header bytes too large → 431",
      "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n" ++
        String.join ((List.range 9).map fun i => s!"X-Header-{i}: {repeatStr "a" 8000}\x0d\n") ++ "\x0d\n", .exact r431)
  ] fun (_, raw, want) => expectServer raw want

#eval checkCases "maxHeaders = 5: every field count of 2–9" #[
    ("field counts 2–9", do
      for count in [2:10] do
        let extra := String.join ((List.range (count - 2)).map fun j => s!"X-Extra-{j}: value\x0d\n")
        try expectServer s!"GET /hc HTTP/1.1\x0d\nHost: example.com\x0d\n{extra}Connection: close\x0d\n\x0d\n"
              (okOr (count ≤ 5) "HTTP/1.1 431") { testConfig with maxHeaders := 5 } (closeInput := true)
        catch e => throw <| IO.userError s!"{count} fields: {e}")
  ] (·.2)

-- Host and Connection take 38 bytes; `X-Payload: ` and its CRLF add 13 to the value.
#eval checkCases "maxHeaderBytes = 200: every field total of 195–205 bytes" #[
    ("field totals 195–205", do
      let baseline := ("Host: example.com\x0d\nConnection: close\x0d\n".toUTF8).size
      for total in [195:206] do
        let value := repeatStr "v" (total - baseline - 13)
        try expectServer s!"GET /hb HTTP/1.1\x0d\nHost: example.com\x0d\nX-Payload: {value}\x0d\nConnection: close\x0d\n\x0d\n"
              (okOr (total ≤ 200) "HTTP/1.1 431") { testConfig with maxHeaderBytes := 200, maxHeaderValueLength := 300 }
              (closeInput := true)
        catch e => throw <| IO.userError s!"{total} bytes: {e}")
  ] (·.2)

#eval checkCases "maxHeaderNameLength = 16: every name length of 1–24" #[
    ("name lengths 1–24", do
      for len in [1:25] do
        try expectServer s!"GET /hnl HTTP/1.1\x0d\nHost: example.com\x0d\n{repeatStr "n" len}: value\x0d\nConnection: close\x0d\n\x0d\n"
              (okOr (len ≤ 16) "HTTP/1.1 400") { testConfig with maxHeaderNameLength := 16 } (closeInput := true)
        catch e => throw <| IO.userError s!"name of {len}: {e}")
  ] (·.2)

#eval checkCases "maxSpaceSequence = 4 (OWS): every count of 0–8 spaces" #[
    ("0", 0), ("1", 1), ("2", 2), ("3", 3), ("4", 4), ("5", 5), ("6", 6), ("7", 7), ("8", 8)
  ] fun (_, spaces) =>
    expectServer s!"GET /ows HTTP/1.1\x0d\nHost: example.com\x0d\nX-OWS:{repeatStr " " spaces}value\x0d\nConnection: close\x0d\n\x0d\n"
      (want := okOr (spaces ≤ 4) "HTTP/1.1 400") (config := { testConfig with maxSpaceSequence := 4 }) (closeInput := true)

#eval checkCases "maxHeaderValueLength = 32: every value length of 0–40" #[
    ("value lengths 0–40", do
      for len in [0:41] do
        try expectServer s!"GET /hvl HTTP/1.1\x0d\nHost: example.com\x0d\nX-Long: {repeatStr "v" len}\x0d\nConnection: close\x0d\n\x0d\n"
              (want := okOr (len ≤ 32) "HTTP/1.1 400") (config := { testConfig with maxHeaderValueLength := 32, maxHeaderBytes := 65536 })
              (closeInput := true)
        catch e => throw <| IO.userError s!"length {len}: {e}")
  ] (·.2)


-- RFC 6585 §5: `maxHeaders` counts field lines, not values.
#eval checkCases "maxHeaders = 15: repeated lines vs one list" #[
    ("16 X-Repeated lines → 431", String.join (List.replicate 16 "X-Repeated: v\x0d\n"), Want.exact r431),
    ("one line with 16 values → 200", s!"X-Repeated: {", ".intercalate (List.replicate 16 "v")}\x0d\n", ok200)
  ] fun (_, fields, want) =>
    expectServer s!"GET / HTTP/1.1\x0d\nHost: example.com\x0d\n{fields}Connection: close\x0d\n\x0d\n" want
      { testConfig with maxHeaders := 15 } (closeInput := true)

#eval checkCases "Client: more fields than maxHeaders fails" #[
    ("10 fields, maxHeaders 5", MachineTester.sending "10 fields, maxHeaders 5" { maxHeaders := 5 }
      |>.send clientGet |>.step
      |>.feed ("HTTP/1.1 200 OK\r\n" ++ String.join ((List.range 10).map fun i => s!"X-F-{i}: v\r\n") ++ "Content-Length: 0\r\n\r\n")
      |>.step |>.assert (·.failed) "expected a header-count failure" |>.run)
  ] (·.2)

/-! ## Leading empty lines (RFC 9112 §2.2) -/

#eval checkCases "maxLeadingEmptyLines = 4: every count of 0–8 CRLFs" #[
    ("0", 0), ("1", 1), ("2", 2), ("3", 3), ("4", 4), ("5", 5), ("6", 6), ("7", 7), ("8", 8)
  ] fun (_, n) =>
    expectServer (repeatStr "\x0d\n" n ++ "GET /le HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
      (want := okOr (n ≤ 4) "HTTP/1.1 400") (config := { testConfig with maxLeadingEmptyLines := 4 }) (closeInput := true)

/-! ## Body size (RFC 9112 §6.3, §7.1; RFC 9110 §15.5.14) -/

/--
Feeds `data` to a server machine `piece` bytes at a time, pulling the body as it arrives. Returns
the machine's error, whether the body completed, and the number of content bytes pulled.
-/
private def runPieces (config : Protocol.H1.Config) (data : ByteArray) (piece : Nat) :
    Option Error × Bool × Nat := Id.run do
  let mut m : Machine .receiving := { config }
  let mut pulled := 0
  let mut complete := false
  let mut i := 0
  while i < data.size && !m.failed do
    m := m.feed (data.extract i (i + piece))
    i := i + piece
    for _ in [0:4] do
      m := m.step.1
      let (m', chunk) := m.pullBody
      m := m'
      if let some c := chunk then
        pulled := pulled + c.chunk.data.size
        complete := complete || c.final
  return (m.error, complete, pulled)

private def chunkedPost : String :=
  "POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n"

#eval checkCases "maxBodySize counts chunk framing (#16282)" #[
    -- 1000 one-byte chunks with ~100-byte extensions: 1000 content bytes, over 100 KB on the wire.
    ("1000 one-byte chunks with long extensions", do
      let ext := s!";name={repeatStr "x" 100}"
      let body := String.join (List.replicate 1000 s!"1{ext}\r\nX\r\n") ++ "0\r\n\r\n"
      let (error, complete, pulled) := runPieces { maxBodySize := 2000 } (chunkedPost ++ body).toUTF8 4096
      ensure (error == some .entityTooLarge && !complete && pulled < 2000)
        s!"framing not counted: {repr error}, complete {complete}, pulled {pulled}"),
    -- The last byte over the limit is the line break that ends the trailer section.
    ("the limit is exactly the body's wire size", do
      let body := "5\r\nhello\r\n3;x=y\r\nabc\r\n0\r\nX-Trace: 1\r\n\r\n"
      let data := (chunkedPost ++ body).toUTF8
      for piece in [data.size, 1] do
        let (error, complete, pulled) := runPieces { maxBodySize := body.utf8ByteSize } data piece
        ensure (error.isNone && complete && pulled == 8)
          s!"exact fit, pieces of {piece}: {repr error}, complete {complete}, pulled {pulled}"
        let (error, complete, _) := runPieces { maxBodySize := body.utf8ByteSize - 1 } data piece
        ensure (error == some .entityTooLarge && !complete)
          s!"one byte over, pieces of {piece}: {repr error}, complete {complete}")
  ] (·.2)

#eval checkCases "Content-Length over maxBodySize: server" #[
    ("very large Content-Length → 413",
      "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 99999999999999999999\x0d\nConnection: close\x0d\n\x0d\nhello")
  ] fun (_, raw) => expectServer raw (.exact r413) (handler := echoHandler)

#eval checkCases "maxBodySize = 64: every Content-Length of 0–84" #[
    ("Content-Length 0–84", do
      for size in [0:85] do
        try expectServer
              (s!"POST /bl-cl HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: {size}\x0d\nConnection: close\x0d\n\x0d\n" ++ repeatStr "a" size)
              (want := okOr (size ≤ 64) "HTTP/1.1 413") (config := { testConfig with maxBodySize := 64 }) (handler := readAllOk)
        catch e => throw <| IO.userError s!"size {size}: {e}")
  ] (·.2)

/-- A chunked body of `total` content bytes in `chunks` equal chunks (the last may be shorter). -/
private def splitChunked (total chunks : Nat) : String := Id.run do
  let chunkSize := (total + chunks - 1) / chunks
  let mut out := ""
  let mut remaining := total
  for _ in [0:chunks] do
    if remaining == 0 then break
    let this := Nat.min chunkSize remaining
    out := out ++ s!"{String.ofList (Nat.toDigits 16 this)}\x0d\n{repeatStr "a" this}\x0d\n"
    remaining := remaining - this
  out ++ "0\x0d\n\x0d\n"

#eval checkCases "maxBodySize = 64 on the wire: totals 0–80 in 1–4 chunks" #[
    ("1 chunk", 1), ("2 chunks", 2), ("3 chunks", 3), ("4 chunks", 4)
  ] fun (_, chunks) => do
    for total in [0:81] do
      let body := splitChunked total chunks
      try expectServer
            (s!"POST /bl-ch HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n" ++ body)
            (want := okOr (body.utf8ByteSize ≤ 64) "HTTP/1.1 413") (config := { testConfig with maxBodySize := 64 }) (handler := readAllOk)
      catch e => throw <| IO.userError s!"total {total}, wire {body.utf8ByteSize}: {e}"

/-! ## Chunk extensions (RFC 9112 §7.1.1) -/

-- A chunk-size line that is still arriving is held to `maxChunkLineLength` by every byte read so
-- far, including those of an extension the read cut off.
#eval checkCases "maxChunkLineLength on an unfinished line" #[
    ("Unfinished chunk-size line over the limit", do
      let input := s!"POST /inc-chunk-line HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: chunked\r\nConnection: keep-alive\r\n\r\n5;{repeatStr "a" 40}".toUTF8
      let trace := feedParts #[input] { maxChunkLineLength := 16 }
      ensure (trace.machine.error == some .badMessage) s!"expected badMessage, got {repr trace.machine.error}")
  ] (·.2)

private def chunkedWith (ext : String) : String :=
  s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5{ext}\x0d\nhello\x0d\n0\x0d\n\x0d\n"

#eval checkCases "Chunk extension limits: server" #[
    ("ext name at 256 bytes → accepted", chunkedWith s!";{repeatStr "a" 256}", Want.status "HTTP/1.1 200", testConfig),
    ("ext name at 257 bytes → 400", chunkedWith s!";{repeatStr "a" 257}", .exact r400, testConfig),
    ("ext token value at 256 bytes → accepted", chunkedWith s!";ext={repeatStr "v" 256}", .status "HTTP/1.1 200", testConfig),
    ("ext token value at 257 bytes → 400", chunkedWith s!";ext={repeatStr "v" 257}", .exact r400, testConfig),
    ("ext quoted value at 256 bytes → accepted", chunkedWith s!";ext=\"{repeatStr "v" 256}\"", .status "HTTP/1.1 200", testConfig),
    ("ext quoted value at 257 bytes → 400", chunkedWith s!";ext=\"{repeatStr "v" 257}\"", .exact r400, testConfig),
    ("16 extensions → accepted", chunkedWith (String.join ((List.range 16).map (s!";e{·}"))), .status "HTTP/1.1 200", testConfig),
    ("17 extensions → 400", chunkedWith (String.join ((List.range 17).map (s!";e{·}"))), .exact r400, testConfig),
    ("1 extension with limit=1 → accepted", chunkedWith ";ext1", .status "HTTP/1.1 200", { testConfig with maxChunkExtensions := 1 }),
    ("2 extensions with limit=1 → 400", chunkedWith ";ext1;ext2", .exact r400, { testConfig with maxChunkExtensions := 1 }),
    ("0 extensions with limit=1 → accepted", chunkedWith "", .status "HTTP/1.1 200", { testConfig with maxChunkExtensions := 1 })
  ] fun (_, raw, want, config) => expectServer raw want config (handler := echoHandler)

#eval checkCases "maxChunkExtNameLength = maxChunkExtValueLength = 4: every pair of lengths 1–8" #[
    ("name and value lengths 1–8", do
      for nameLen in [1:9] do
        for valueLen in [1:9] do
          let raw := s!"POST /ext-limit HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n1;{repeatStr "n" nameLen}={repeatStr "v" valueLen}\x0d\nx\x0d\n0\x0d\n\x0d\n"
          try expectServer raw (if nameLen ≤ 4 ∧ valueLen ≤ 4 then .status "HTTP/1.1 200" else .exact r400)
                { testConfig with maxChunkExtNameLength := 4, maxChunkExtValueLength := 4 } (handler := echoHandler)
          catch e => throw <| IO.userError s!"name {nameLen}, value {valueLen}: {e}")
  ] (·.2)

#eval checkCases "maxChunkExtensions = 2: every count of 0–5" #[
    ("0", 0), ("1", 1), ("2", 2), ("3", 3), ("4", 4), ("5", 5)
  ] fun (_, n) =>
    expectServer
      s!"POST /ext-count HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n1{String.join ((List.range n).map (s!";n{·}=v"))}\x0d\nx\x0d\n0\x0d\n\x0d\n"
      (want := if n ≤ 2 then .status "HTTP/1.1 200" else .exact r400) (config := { testConfig with maxChunkExtensions := 2 })
      (handler := echoHandler)


-- RFC 9112 §7.1: leading zeros are part of the chunk line, so `maxChunkLineLength` bounds them.
#eval checkCases "65 536 leading zeros in a chunk size" #[
    ("0…0a → 400", s!"{repeatStr "0" 65536}a\x0d\n{repeatStr "x" 10}\x0d\n0\x0d\n\x0d\n")
  ] fun (_, chunked) =>
    checkHandler ("POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n" ++ chunked)
      readAllOk (.exact r400) (closeInput := true)

/-! ## Trailers (RFC 9112 §7.1.2) -/

private def trailerConfig : Std.Http.Config := { lingeringTimeout := 3000, generateDate := false }

private def chunkedTrailers (trailers : String) : String :=
  s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\n{trailers}\x0d\n"

#eval checkCases "Trailer limits: server" #[
    ("trailer name of 256 characters", chunkedTrailers s!"{repeatStr "X" 256}: value\x0d\n", Want.status "HTTP/1.1 200", trailerConfig),
    ("trailer name of 257 characters", chunkedTrailers s!"{repeatStr "X" 257}: value\x0d\n", .exact r400, trailerConfig),
    ("trailer value of 8192 characters", chunkedTrailers s!"X-Exact: {repeatStr "v" 8192}\x0d\n", .status "HTTP/1.1 200", trailerConfig),
    ("trailer value of 8193 characters", chunkedTrailers s!"X-Too-Long: {repeatStr "v" 8193}\x0d\n", .exact r400, trailerConfig),
    ("maxTrailerHeaders 2: 2 trailers", chunkedTrailers "T1: a\x0d\nT2: b\x0d\n", .status "HTTP/1.1 200", { trailerConfig with maxTrailerHeaders := 2 }),
    ("maxTrailerHeaders 2: 3 trailers", chunkedTrailers "T1: a\x0d\nT2: b\x0d\nT3: c\x0d\n", .exact r400, { trailerConfig with maxTrailerHeaders := 2 }),
    ("maxTrailerHeaders 0: any trailer", chunkedTrailers "X-Trailer: rejected\x0d\n", .exact r400, { trailerConfig with maxTrailerHeaders := 0 }),
    ("maxTrailerHeaders 0: no trailer", chunkedTrailers "", .status "HTTP/1.1 200", { trailerConfig with maxTrailerHeaders := 0 })
  ] fun (_, raw, want, config) => expectServer raw want config (handler := echoHandler)

#eval checkCases "maxTrailerHeaders = 2: every count of 0–5" #[
    ("0", 0), ("1", 1), ("2", 2), ("3", 3), ("4", 4), ("5", 5)
  ] fun (_, n) =>
    expectServer
      s!"POST /trailers HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n1\x0d\na\x0d\n0\x0d\n{String.join ((List.range n).map (s!"X{·}-t: v\x0d\n"))}\x0d\n"
      (want := if n ≤ 2 then .status "HTTP/1.1 200" else .exact r400) (config := { testConfig with maxTrailerHeaders := 2 })
      (handler := echoHandler)

/-! ## Buffered input -/

-- Unread buffered input stays bounded, so a stalled body consumer cannot grow it without limit.
#eval checkCases "Buffered input cap" #[
    ("Buffered input cap triggers entityTooLarge", do
      let cfg : Protocol.H1.Config := {
        maxBodySize := 32, maxHeaderBytes := 16, maxStartLineLength := 16, maxChunkLineLength := 16 }
      let cap := cfg.maxBodySize + cfg.maxHeaderBytes + cfg.maxStartLineLength + cfg.maxChunkLineLength
      let machine1 := ({ config := cfg } : Machine .receiving).feed (ByteArray.mk (Array.replicate (cap + 1) 97))
      ensure machine1.failed "expected machine to fail on oversized buffered input"
      ensure (machine1.error == some .entityTooLarge) s!"expected entityTooLarge failure, got {repr machine1.error}")
  ] (·.2)
