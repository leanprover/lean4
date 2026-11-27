import Std.Http
import Std.Http.Protocol.H1.Input

open Std Internal Parsec ByteArray
open Std.Http.Protocol.H1

/-!
Checks `LineScan.read`, the resumable scan of incomplete lines (#16522), against the line parsers it
stands in for. Every prefix of each generated line is read as one more byte arriving, with the scan
kept across reads, and whenever the scan answers without running the parser, the parser run on that
prefix must return `.eof` (before `limit`, for the lines that have one). The lines are valid lines,
their random mutations, and random strings over each grammar's bytes, under the default limits and
tiny ones that put every count at its limit. `LINE_SCAN_CASES` scales the number of cases.
-/

/-- A line kind, its parser, and the `limit` the machine passes for it. -/
structure Grammar where
  name : String
  kind : LineKind
  parser : Config → Parser Unit
  limit : Config → Option Nat
  templates : Array String
  alphabet : Array String
  /-- Inputs the machine never reads with this kind are skipped. -/
  admits : ByteArray → Bool := fun _ => true

def grammars : Array Grammar := #[
  { name := "request-line", kind := .requestLine
    parser := fun c => discard (parseRequestLineRawVersion c), limit := fun _ => none
    templates := #["GET / HTTP/1.1\r\n", "\r\n\r\nPOST /a?b=c HTTP/1.0\r\n", "OPTIONS * HTTP/1.1\r\n",
      "CONNECT a.b:80 HTTP/1.1\r\n", "GET http://h/p HTTP/1.1\r\n", "AAAAAAAA /x HTTP/1.1\r\n",
      "GET /%41%zz HTTP/2.0\r\n", "HEAD /[::1] HTTP/1.1\r\n"]
    alphabet := #["G", "E", "T", "A", " ", "/", "a", "?", "%", "H", "P", "1", ".", "0", "\r", "\n",
      "#", "\t", ":", "*", "[", "\x00", "\x7f", "é", "HTTP/1.1", "GET", "  "] },
  { name := "status-line", kind := .statusLine
    parser := fun c => discard (parseStatusLineRawVersion c), limit := fun c => some c.maxStartLineLength
    templates := #["HTTP/1.1 200 OK\r\n", "HTTP/1.0 404\r\n", "HTTP/1.1 100 \r\n", "HTTP/1.1 999 x y\r\n",
      "HTTP/2.0 200 OK\r\n"]
    alphabet := #["H", "T", "P", "/", "1", ".", "0", "2", " ", "\r", "\n", "O", "K", "\t", "\x01",
      "é", "\x7f", "HTTP/1.1"] },
  { name := "field-line", kind := .fieldLine
    parser := fun c => discard (parseSingleHeader c), limit := fun _ => none
    templates := #["Host: a\r\n", "X:\r\n", "X-Long-Name:   v  a  l  \r\n", "\r\n", "A:\t\tb\r\n",
      "Content-Length: 10\r\n", "Set-Cookie: a=b; c=\"d\"\r\n"]
    alphabet := #["a", "B", "-", ":", " ", "\t", "\r", "\n", "\"", "é", "\x00", "\x7f", "\x80", "v",
      "(", ";", "=", "  "] },
  { name := "field-line (typed)", kind := .fieldLine
    parser := fun c => discard (parseHeaderField c), limit := fun _ => none
    templates := #["Host: a\r\n", "X:\r\n", "X-Long-Name:   v  a  l  \r\n", "\r\n", "A:\t\tb\r\n",
      "Content-Length: 10\r\n", "Set-Cookie: a=b; c=\"d\"\r\n", "Accept-Language: é\r\n"]
    alphabet := #["a", "B", "-", ":", " ", "\t", "\r", "\n", "\"", "é", "\x00", "\x7f", "\x80", "v",
      "(", ";", "=", "  "] },
  { name := "trailer-line", kind := .fieldLine
    parser := fun c => discard (parseTrailerHeader c true), limit := fun _ => none
    templates := #["X-Sum: 1\r\n", "Host: a\r\n", "Expect: 1\r\n", "\r\n"]
    alphabet := #["a", "H", "o", "s", "t", ":", " ", "\r", "\n", "\t", "x"] },
  { name := "obs-fold", kind := .obsFold
    parser := fun c => discard (parseObsFoldContinuation c), limit := fun _ => none
    templates := #[" more\r\n", "\t\tx y \r\n", " \r\n"]
    alphabet := #[" ", "\t", "a", "\r", "\n", "\x01", "é", ":"]
    admits := fun b => b.size == 0 || b[0]! == 32 || b[0]! == 9 },
  { name := "chunk-size", kind := .chunkSize
    parser := fun c => discard (parseChunkSize c), limit := fun c => some c.maxChunkLineLength
    templates := #["1a\r\n", "0\r\n", "000\r\n", "5;a=b\r\n", "5 ; a = \"x\\\"y\" ;b\r\n",
      "10;n;m=v;q=\"\"\r\n", "ffffffffffffffff\r\n", "1ffffffffffffffff\r\n", "4;a=\"é\"\r\n",
      "3;a ;b\r\n", "3;a \r\n"]
    alphabet := #["0", "1", "a", "F", "g", ";", "=", " ", "\t", "\"", "\\", "\r", "\n", "x", "é",
      "\x01", ",", "  "] }]

def configs : Array (String × Config) := #[
  ("default", {}),
  ("tiny", { maxUriLength := 4, maxStartLineLength := 3, maxHeaderNameLength := 3,
             maxHeaderValueLength := 4, maxSpaceSequence := 2, maxLeadingEmptyLines := 1,
             maxReasonPhraseLength := 2, maxChunkExtensions := 2, maxChunkExtNameLength := 2,
             maxChunkExtValueLength := 2, maxChunkLineLength := 24 }),
  ("edge", { maxUriLength := 1, maxStartLineLength := 0, maxHeaderNameLength := 1,
             maxHeaderValueLength := 1, maxSpaceSequence := 0, maxLeadingEmptyLines := 0,
             maxReasonPhraseLength := 0, maxChunkExtensions := 0, maxChunkExtNameLength := 1,
             maxChunkExtValueLength := 0, maxChunkLineLength := 12 }),
  ("one", { maxUriLength := 2, maxHeaderNameLength := 2, maxHeaderValueLength := 2,
            maxSpaceSequence := 1, maxReasonPhraseLength := 1, maxChunkExtensions := 1,
            maxChunkExtNameLength := 2, maxChunkExtValueLength := 1 }),
  ("nows", { maxUriLength := 0, maxHeaderValueLength := 2, maxSpaceSequence := 0,
             maxReasonPhraseLength := 1, maxChunkExtNameLength := 1, maxChunkExtValueLength := 1 }),
  ("zero", { maxUriLength := 0, maxHeaderNameLength := 0, maxHeaderValueLength := 0,
             maxSpaceSequence := 1, maxReasonPhraseLength := 0, maxLeadingEmptyLines := 0,
             maxChunkExtensions := 0, maxChunkExtNameLength := 0, maxChunkExtValueLength := 1,
             maxChunkLineLength := 10 })]

/-- A small linear congruential generator, so the cases are the same on every run. -/
def nextRand (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

def below (s : Nat) (n : Nat) : Nat × Nat :=
  let s := nextRand s
  ((s / 65536) % (max n 1), s)

def randomLine (g : Grammar) (seed : Nat) : ByteArray := Id.run do
  let (mode, s) := below seed 3
  let mut s := s
  let mut out : ByteArray := .empty
  if mode == 0 then
    let (len, s') := below s 14
    s := s'
    for _ in [0:len] do
      let (i, s') := below s g.alphabet.size
      s := s'
      out := out ++ g.alphabet[i]!.toUTF8
  else
    let (i, s') := below s g.templates.size
    s := s'
    out := g.templates[i]!.toUTF8
    -- Long elements put counts at the default limits too.
    let (grow, s') := below s 4
    s := s'
    if grow == 0 then
      let (at_, s') := below s (out.size + 1)
      let (n, s'') := below s' 300
      s := s''
      let (j, s') := below s g.alphabet.size
      s := s'
      let filler := String.join (List.replicate n g.alphabet[j]!)
      out := out.extract 0 at_ ++ filler.toUTF8 ++ out.extract at_ out.size
    let (edits, s') := below s (if mode == 1 then 1 else 4)
    s := s'
    for _ in [0:edits] do
      let (op, s') := below s 3
      let (at_, s'') := below s' (out.size + 1)
      let (j, s''') := below s'' g.alphabet.size
      s := s'''
      let piece := g.alphabet[j]!.toUTF8
      out :=
        if op == 0 then out.extract 0 at_ ++ piece ++ out.extract at_ out.size
        else if op == 1 then out.extract 0 at_ ++ out.extract (at_ + 1) out.size
        else out.extract 0 at_ ++ piece ++ out.extract (at_ + 1) out.size
  return out

/--
Reads every prefix of `line` (after `junk` bytes already consumed) one byte at a time and checks each
answer the scan gives without the parser. Returns the number of parser runs.
-/
def checkLine (g : Grammar) (cname : String) (c : Config) (junk : Nat) (line : ByteArray) :
    Except String Nat := do
  let pre := ByteArray.mk (Array.replicate junk 120)
  let mut scan : LineScan := {}
  let mut runs := 0
  for k in [0:line.size + 1] do
    let input : ByteArray.Iterator := ⟨pre ++ line.extract 0 k, junk⟩
    let (scan', result) := LineScan.read c g.kind false (g.limit c) (g.parser c) scan input
    match result with
    | some r =>
      runs := runs + 1
      match r with
      | .error _ .eof => scan := scan'
      | _ => return runs
    | none =>
      let ok := match g.parser c input with
        | .error it .eof => (g.limit c).all (input.remainingBytes - it.remainingBytes < ·)
        | _ => false
      unless ok do
        throw s!"{g.name} [{cname}] scan says incomplete but the parser does not, at {k} bytes of {repr (String.fromUTF8! (line.extract 0 k) |>.quote)}"
      scan := scan'
  return runs

def main : IO Unit := do
  let cases := ((← IO.getEnv "LINE_SCAN_CASES").bind String.toNat?).getD 40
  let mut seed := 7
  let mut total := 0
  let mut runs := 0
  let mut bytes := 0
  for g in grammars do
    for (cname, c) in configs do
      let lines := g.templates.map (·.toUTF8) ++ (Array.range cases).map fun i =>
        randomLine g (seed + i * 7919)
      seed := seed + 104729
      for line in lines do
        unless g.admits line do continue
        match checkLine g cname c (line.size % 3) line with
        | .ok n => runs := runs + n; total := total + 1; bytes := bytes + line.size + 1
        | .error e => throw <| IO.userError e
  -- The parser runs a bounded number of times per line, not once per byte.
  unless runs * 3 < bytes do
    throw <| IO.userError s!"the parser ran {runs} times over {bytes} reads"
  if (← IO.getEnv "LINE_SCAN_CASES").isSome then
    IO.println s!"{total} lines, {bytes} reads, {runs} parser runs"

#eval main
