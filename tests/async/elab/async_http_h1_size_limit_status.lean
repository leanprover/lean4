import Std.Http

open Std Http
open Std.Http.Protocol.H1

/-!
Tests the answer to a single field or chunk over a size limit. A field name over
`maxHeaderNameLength` or a field value over `maxHeaderValueLength` gets 431, as too many fields or
too many field bytes do (RFC 6585 §5: "when a single header field is at fault"). A chunk size of more
than 16 significant hex digits gets 413, as a chunk over `maxChunkSize` does. A field or size that
only ends in an invalid byte at the limit is not too long and gets 400. A client fails with the same
errors.

Each request is fed as every prefix and as two reads split at every byte boundary, so the answer
does not depend on where a read ends (#16035).
-/

/-- Feeds `parts` in order, stepping and draining the body after each, and returns the machine's
error and its output. -/
def feedParts (parts : List ByteArray) (config : Protocol.H1.Config := {}) :
    Option Error × String := Id.run do
  let mut m : Machine .receiving := { config }
  let mut out := ByteArray.empty
  for part in parts do
    m := m.feed part
    for _ in [0:4] do
      let (m', r) := m.step
      m := m'
      out := out ++ r.output.toByteArray
      while m.canPullBody do
        let (m', chunk?) := m.pullBody
        m := m'
        if chunk?.isNone then break
  return (m.error, String.fromUTF8! out)

def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

/--
`waits ++ rest` is a request that goes over a limit, or turns invalid, at the first byte of `rest`.
Every prefix of at most `waits.size` bytes gets no answer yet. Every longer prefix, and the whole
input split at any byte boundary, fails with `error` and gets a response starting with `status`.
-/
def expectRejectedAt (name : String) (waits rest : String) (error : Error) (status : String)
    (config : Protocol.H1.Config := {}) : IO Unit := do
  let waits := waits.toUTF8
  let whole := waits ++ rest.toUTF8
  for i in [0:whole.size + 1] do
    let pfx := whole.extract 0 i
    let (err, out) := feedParts [pfx] config
    if i ≤ waits.size then
      check (err.isNone && out.isEmpty)
        s!"{name}: after {i} bytes expected no answer yet, got {repr err} {out.quote}"
    else
      check (err == some error && out.startsWith status)
        s!"{name}: after {i} bytes expected {repr error} and {status.quote}, got {repr err} {out.quote}"
    let (err, out) := feedParts [pfx, whole.extract i whole.size] config
    check (err == some error && out.startsWith status)
      s!"{name}: split at byte {i}, expected {repr error} and {status.quote}, got {repr err} {out.quote}"

def expect431 (name waits rest : String) (config : Protocol.H1.Config := {}) : IO Unit :=
  expectRejectedAt name waits rest .headersTooLarge "HTTP/1.1 431 " config

def expect413 (name waits rest : String) (config : Protocol.H1.Config := {}) : IO Unit :=
  expectRejectedAt name waits rest .entityTooLarge "HTTP/1.1 413 " config

def expect400 (name waits rest : String) (config : Protocol.H1.Config := {}) : IO Unit :=
  expectRejectedAt name waits rest .badMessage "HTTP/1.1 400 " config

def expectAccepted (name req : String) (config : Protocol.H1.Config := {}) : IO Unit := do
  let (err, out) := feedParts [req.toUTF8] config
  check (err.isNone && out.isEmpty) s!"{name}: expected no error, got {repr err} {out.quote}"

/-- Runs every case and throws once, listing the first failure of each failing case. -/
def runCases (cases : List (IO Unit)) : IO Unit := do
  let mut errors : Array String := #[]
  for c in cases do
    try c catch e => errors := errors.push (toString e)
  unless errors.isEmpty do throw (IO.userError ("\n".intercalate errors.toList))

def repeatStr (s : String) (n : Nat) : String := String.join (List.replicate n s)

def head : String := "GET / HTTP/1.1\r\nHost: a\r\n"

def small : Protocol.H1.Config := { maxHeaderNameLength := 8, maxHeaderValueLength := 16 }

-- `small` allows an 8-byte name and a 16-byte value.
#eval runCases [
  expectAccepted "name at the limit" s!"{head}{repeatStr "N" 8}: v\r\n\r\n" small,
  expectAccepted "value at the limit" s!"{head}X: {repeatStr "v" 16}\r\n\r\n" small,
  expectAccepted "value at the limit, then trailing OWS" s!"{head}X: {repeatStr "v" 16} \t \r\n\r\n" small,
  expectAccepted "value with inner SP at the limit" s!"{head}X: {repeatStr "v" 8} {repeatStr "v" 7}\r\n\r\n" small,
  expect431 "name one byte past the limit" s!"{head}{repeatStr "N" 8}" "N: v\r\n\r\n" small,
  expect431 "value one byte past the limit" s!"{head}X: {repeatStr "v" 16}" "v\r\n\r\n" small,
  expect431 "value continues after SP at the limit" s!"{head}X: {repeatStr "v" 16} " "v\r\n\r\n" small,
  -- These end at the limit with a byte that is invalid there, so they are malformed, not too long.
  expect400 "name at the limit, then SP before the colon" s!"{head}{repeatStr "N" 8}" " : v\r\n\r\n" small,
  expect400 "value at the limit, then NUL" s!"{head}X: {repeatStr "v" 16}" "\x00\r\n\r\n" small]

#eval runCases [
  expectAccepted "default name limit" s!"{head}{repeatStr "N" 256}: v\r\n\r\n",
  expectAccepted "default value limit" s!"{head}X: {repeatStr "v" 8192}\r\n\r\n",
  do
    let (err, out) := feedParts [s!"{head}{repeatStr "N" 257}: v\r\n\r\n".toUTF8]
    check (err == some .headersTooLarge && out.startsWith "HTTP/1.1 431 ")
      s!"257-byte name: got {repr err} {out.quote}",
  do
    let (err, out) := feedParts [s!"{head}X: {repeatStr "v" 8193}\r\n\r\n".toUTF8]
    check (err == some .headersTooLarge && out.startsWith "HTTP/1.1 431 ")
      s!"8193-byte value: got {repr err} {out.quote}"]

def chunked : String := "POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n"

-- A 17th significant digit fails at once; sixteen fit the parser, and the size is checked against
-- `maxChunkSize` once its line ends.
#eval runCases [
  expect413 "17 significant hex digits" s!"{chunked}{repeatStr "f" 16}" "f\r\nabc\r\n0\r\n\r\n",
  expect413 "17 digits after leading zeros" s!"{chunked}000{repeatStr "f" 16}" "f\r\nabc\r\n0\r\n\r\n",
  expect413 "16 digits over maxChunkSize" s!"{chunked}{repeatStr "f" 16}\r" "\nabc\r\n0\r\n\r\n",
  expect400 "16 digits, then an invalid byte" s!"{chunked}{repeatStr "f" 16}" "g\r\nabc\r\n0\r\n\r\n"]

/-- Sends a GET, feeds `response` as a client, and returns the machine's error. -/
def clientError (response : String) (config : Protocol.H1.Config := {}) : Option Error := Id.run do
  let mut m : Machine .sending := { config }
  m := m.send { method := .get, version := .v11, uri := RequestTarget.originForm! "/",
                headers := Headers.empty.insert! "Host" "a" }
  m := m.feed response.toUTF8
  for _ in [0:6] do
    let (m', _) := m.step
    m := m'
    while m.canPullBody do
      let (m', chunk?) := m.pullBody
      m := m'
      if chunk?.isNone then break
  return m.error

#eval runCases <| [
    ("name over the limit", s!"HTTP/1.1 200 OK\r\n{repeatStr "N" 9}: v\r\nContent-Length: 0\r\n\r\n",
      small, Error.headersTooLarge),
    ("value over the limit", s!"HTTP/1.1 200 OK\r\nX: {repeatStr "v" 17}\r\nContent-Length: 0\r\n\r\n",
      small, .headersTooLarge),
    -- A client unfolds obs-fold (RFC 9112 §5.2); the unfolded value is held to the same limit.
    ("value over the limit after unfolding",
      s!"HTTP/1.1 200 OK\r\nX: {repeatStr "v" 10}\r\n {repeatStr "v" 10}\r\nContent-Length: 0\r\n\r\n",
      small, .headersTooLarge),
    ("17-digit chunk size",
      s!"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n{repeatStr "f" 17}\r\nabc\r\n0\r\n\r\n",
      {}, .entityTooLarge)
  ].map fun (name, response, config, error) => do
    let err := clientError response config
    check (err == some error) s!"client, {name}: expected {repr error}, got {repr err}"
