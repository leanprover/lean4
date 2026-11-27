/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Parsec.ByteArray
public import Std.Http.Protocol.H1.Config
public import Std.Http.Protocol.H1.Parser

public section

/-!
# Incremental input

The reader's input buffer and the operations that read it without going back over bytes already
examined:

- `Input.append` adds a read to the unread input, copying the unread bytes only when most of the
  buffer is consumed.
- `LineScan` resumes the scan of a line that has not fully arrived, so a line fed in pieces is not
  parsed again from its start on every read (issue #16522).
- `readFixed` and `readChunkData` take body bytes straight from the buffer, sharing it when a read
  is all body.

## Line scanning

A line parser run on a line that has not fully arrived returns `.eof` or fails, and the machine asks
for more input on `.eof`. `LineScan` finds most of those `.eof` verdicts without running the parser:
it follows the line's grammar byte by byte from where the previous read stopped, and only marks a
byte *plain* when the parser run on the input up to and including it returns `.eof`. At any other
byte (a line end, a delimiter whose meaning the parser decides, a byte that is invalid there, or a
count reaching its limit) the scan stops and the parser runs on the whole line, as it always did, so
it gives every verdict: the error of an invalid byte, the limits, and the parsed line. A parser run
that returns `.eof` there lets the scan pass that byte and go on.

So the parser runs at most a few times per line whatever the number of reads, the scan examines each
byte once, and the outcome of every read is the parser's own.
-/

namespace Std.Http.Protocol.H1

open Std Std.Internal Parsec ByteArray Internal.Char

set_option linter.all true

/--
Appends a read to the unread `input`, keeping the bytes not yet read. The buffer is extended in place
while fewer than half of its bytes are consumed; otherwise the unread bytes move to a new buffer, so
each byte is copied a bounded number of times and the buffer stays under twice the unread input.
-/
def Input.append (input : ByteArray.Iterator) (data : ByteArray) : ByteArray.Iterator :=
  let arr := input.array
  let idx := input.idx
  if idx ≥ arr.size then
    data.iter
  else if 2 * idx ≥ arr.size then
    let unread := arr.size - idx
    let buf := arr.copySlice idx (ByteArray.emptyWithCapacity (unread + data.size)) 0 unread
    (data.copySlice 0 buf unread data.size).iter
  else
    ⟨arr ++ data, idx⟩

/--
The next `n` bytes of `input`. When they are the whole buffer it is returned as is, without a copy.
-/
@[inline]
def Input.bytes (input : ByteArray.Iterator) (n : Nat) : ByteArray :=
  if input.idx == 0 && n == input.array.size then input.array
  else input.array.extract input.idx (input.idx + n)

/-! ## Body data -/

/--
The outcome of reading body data from the input.
-/
inductive BodyRead where
  /--
  The read needs more input: nothing is buffered, or the data of a chunk is but its line break is
  not yet whole.
  -/
  | needMore

  /--
  The bytes after a chunk's data are not its line break.
  -/
  | invalid

  /--
  `bytes` were read, `rest` is the input after them (and after a chunk's line break), and
  `remaining` bytes of the body or chunk are still to come.
  -/
  | data (bytes : ByteArray) (rest : ByteArray.Iterator) (remaining : Nat)

/--
Reads up to `size` bytes of a fixed-length body: what is buffered, or `.needMore` when nothing is.
-/
@[inline]
def readFixed (input : ByteArray.Iterator) (size : Nat) : BodyRead :=
  let avail := input.remainingBytes
  if avail == 0 then
    .needMore
  else
    let n := min avail size
    .data (Input.bytes input n) (input.forward n) (size - n)

/--
Reads up to `size` bytes of a chunk's data. The data is complete (`remaining = 0`) only together with
the `CRLF` after it, which is consumed with it.
-/
@[inline]
def readChunkData (input : ByteArray.Iterator) (size : Nat) : BodyRead :=
  let avail := input.remainingBytes
  if avail == 0 then
    .needMore
  else if avail < size then
    .data (Input.bytes input avail) (input.forward avail) (size - avail)
  else
    let i := input.idx + size
    match input.array[i]?, input.array[i + 1]? with
    | none, _ => .needMore
    | some 13, none => .needMore
    | some 13, some 10 => .data (Input.bytes input size) (input.forward (size + 2)) 0
    | _, _ => .invalid

/-! ## Line scanning -/

/--
The grammar a line is read with.
-/
inductive LineKind where
  /--
  A request line, with the empty lines a server ignores before it (`parseRequestLineRawVersion`).
  -/
  | requestLine

  /--
  A status line (`parseStatusLineRawVersion`).
  -/
  | statusLine

  /--
  A field line of the header or trailer section, or the empty line that ends it
  (`parseSingleHeader`, `parseTrailerHeader`).
  -/
  | fieldLine

  /--
  A line continuing a field value after an obsolete line folding (`parseObsFoldContinuation`).
  -/
  | obsFold

  /--
  A chunk-size line (`parseChunkSize`).
  -/
  | chunkSize
deriving Inhabited, BEq, Repr

/--
How far into its grammar the scan of a line is. `count` and `exts` of `LineScan` qualify it.
-/
inductive LineScan.Phase where
  /--
  Past a byte whose meaning only the parser decides: every byte stops the scan.
  -/
  | opaque

  /--
  At the start of a request line or after an empty line before it.
  -/
  | reqLead

  /--
  After the `CR` of an empty line before a request line.
  -/
  | reqLeadCR

  /--
  In the method, `count` bytes long.
  -/
  | reqMethod

  /--
  In the request-target, `count` bytes long.
  -/
  | reqTarget

  /--
  In the HTTP version of a request line, `count` bytes in.
  -/
  | reqVersion

  /--
  In the HTTP version of a status line, `count` bytes in.
  -/
  | stVersion

  /--
  In the status code, `count` digits in.
  -/
  | stCode

  /--
  In the reason phrase, `count` bytes long.
  -/
  | stReason

  /--
  At the start of a field line.
  -/
  | fieldStart

  /--
  In a field name, `count` bytes long.
  -/
  | fieldName

  /--
  In the whitespace before a field value, `count` bytes long.
  -/
  | fieldOws

  /--
  In a field value, `count` bytes long.
  -/
  | fieldValue

  /--
  In the whitespace after a field value of `maxHeaderValueLength` bytes, `count` bytes long.
  -/
  | fieldTrail

  /--
  In the leading zeros of a chunk size, `count` of them.
  -/
  | chunkZeros

  /--
  In the significant digits of a chunk size, `count` of them.
  -/
  | chunkDigits

  /--
  After a quoted chunk-extension value.
  -/
  | chunkExtStart

  /--
  In the whitespace before the `;` of a chunk extension, `count` bytes long.
  -/
  | chunkBws

  /--
  In the whitespace after the `;` of a chunk extension, `count` bytes long.
  -/
  | chunkSemi

  /--
  In a chunk-extension name, `count` bytes long.
  -/
  | chunkName

  /--
  In the whitespace after a chunk-extension name, `count` bytes long.
  -/
  | chunkNameWs

  /--
  In the whitespace after the `=` of a chunk extension, `count` bytes long.
  -/
  | chunkEqWs

  /--
  In a token chunk-extension value, `count` bytes long.
  -/
  | chunkToken

  /--
  In a quoted chunk-extension value, `count` bytes of content long.
  -/
  | chunkQuoted

  /--
  After the backslash of a quoted-pair in a quoted chunk-extension value.
  -/
  | chunkEscape
deriving Inhabited, BEq, Repr

/--
The scan of the line at the start of the unread input, kept across reads while the line is
incomplete. Inactive scans (the default) mean that no scan of the current line exists yet.
-/
structure LineScan where
  /--
  The grammar the line is scanned with.
  -/
  kind : LineKind := .requestLine

  /--
  The number of times the parser returned `.eof` on the line before its scan started. A line that
  arrives in one or two reads is only parsed: scanning it would cost more than parsing it again.
  -/
  tries : Nat := 0

  /--
  Whether the fields below hold a scan of the line at the start of the unread input.
  -/
  active : Bool := false

  /--
  The number of bytes of the line already scanned, from the start of the unread input.
  -/
  scanned : Nat := 0

  /--
  The grammar position after the scanned bytes.
  -/
  phase : LineScan.Phase := .opaque

  /--
  The length of the current element (method, target, name, value, whitespace run, digits).
  -/
  count : Nat := 0

  /--
  The number of chunk extensions started on a chunk-size line.
  -/
  exts : Nat := 0
deriving Inhabited, Repr

namespace LineScan

/--
Where the scan of a line of `kind` starts.
-/
def initial : LineKind → Phase
  | .requestLine => .reqLead
  | .statusLine => .stVersion
  | .fieldLine => .fieldStart
  | .obsFold => .fieldOws
  | .chunkSize => .chunkZeros

/--
A fresh scan of a line of `kind`.
-/
def start (kind : LineKind) : LineScan :=
  { kind, active := true, phase := initial kind }

/-- What one byte does to the scan: `plain` when the parser still returns `.eof`. -/
private structure Next where
  plain : Bool
  phase : Phase
  count : Nat
  exts : Nat

@[inline] private def plain (phase : Phase) (count : Nat) (exts : Nat := 0) : Next :=
  ⟨true, phase, count, exts⟩

@[inline] private def event (phase : Phase) (count : Nat) : Next :=
  ⟨false, phase, count, 0⟩

@[inline] private def stop : Next :=
  ⟨false, .opaque, 0, 0⟩

-- The byte classes of the parsers in `H1.Parser`, which these must equal.
@[inline] private def isTchar (b : UInt8) : Bool := tchar (Char.ofUInt8 b)
@[inline] private def isOwsByte (b : UInt8) : Bool := Internal.Char.ows (Char.ofUInt8 b)
@[inline] private def isFieldVChar (b : UInt8) : Bool := fieldContent (Char.ofUInt8 b)
@[inline] private def isReasonPhraseByte (b : UInt8) : Bool := fieldContent (Char.ofUInt8 b)
@[inline] private def isQdText (b : UInt8) : Bool := qdtext (Char.ofUInt8 b)

/-- Byte `p` of `HTTP/<digit>.<digit>`. -/
@[inline] private def versionByte (p : Nat) (b : UInt8) : Bool :=
  match p with
  | 0 => b == 'H'.toUInt8
  | 1 | 2 => b == 'T'.toUInt8
  | 3 => b == 'P'.toUInt8
  | 4 => b == '/'.toUInt8
  | 6 => b == '.'.toUInt8
  | _ => isDigitByte b

/-
Why each `plain` transition below leaves the parser at `.eof`, given that every earlier byte was
plain or a stop the parser passed with `.eof`:

- Taking a byte of an element below its limit: `takeRunUpTo`/`takeRunUpTo1` at the end of the
  input fail with `.eof` below their limit, `digit`, `any`, `skipByte`, `skipBytes` fail with `.eof`
  there, and no `optional`/`orElse` around them catches an `.eof` after bytes were consumed.
- Taking the byte that brings an element to its limit: `takeRunUpTo` then succeeds without looking
  further, the check of whether the element goes on (`peekWhen?`) sees the end of the input, and the
  next parser needs a byte. The byte after it overflows the element when it is one of its bytes,
  which stops the scan; any other byte means what it means after a shorter element. A token
  chunk-extension value is the exception: at its limit the extension is complete, and is checked
  against `maxChunkExtensions` at once.
- A delimiter that ends an element (`SP` after a method, `:` after a field name, `SP` after a version
  or status code, `;` and `=` in chunk extensions, `CR`): the element stopped on a byte, the
  delimiter is consumed, and what follows starts with one of the parsers above. A `CR` is followed
  by `LF` in `crlf`, which fails with `.eof`.
- A `SP` that ends a request-target is a stop: the target is parsed as a URI there and may fail.
- In a chunk-size line, an extension is checked against `maxChunkExtensions` when it is complete,
  so with more extensions than that every byte completing one stops the scan.
-/

/-
After `;` and `=`, `ows` with `maxSpaceSequence = 0` succeeds at the end of the input instead of
returning `.eof`, and the name or value token that follows fails there when its limit is 0.
-/
@[inline] private def semi (c : Config) (exts : Nat) : Next :=
  if 0 < c.maxChunkExtNameLength then plain .chunkSemi 0 (exts + 1) else stop

@[inline] private def equals (c : Config) (exts : Nat) : Next :=
  if 0 < c.maxChunkExtValueLength then plain .chunkEqWs 0 exts else stop

/-- Shared by the chunk-size phases: the byte after a chunk size or a complete extension. -/
@[inline] private def chunkAfter (c : Config) (exts : Nat) (b : UInt8) : Next :=
  if isOwsByte b then
    if 1 ≤ c.maxSpaceSequence then plain .chunkBws 1 exts else stop
  else if b == ';'.toUInt8 then semi c exts
  else if b == '\r'.toUInt8 then plain .opaque 0
  else stop

/-- A byte of a whitespace run in a chunk-size line, which `ows` bounds by `maxSpaceSequence`. -/
@[inline] private def chunkWs (c : Config) (phase : Phase) (n exts : Nat) : Next :=
  if n + 1 ≤ c.maxSpaceSequence then plain phase (n + 1) exts else stop

/-- A byte of a field value. At `maxHeaderValueLength` only whitespace and the line end may follow. -/
@[inline] private def fieldValueByte (c : Config) (n : Nat) : Next :=
  if n + 1 < c.maxHeaderValueLength then plain .fieldValue (n + 1)
  else if n + 1 == c.maxHeaderValueLength then plain .fieldTrail 0
  else stop

/--
A byte of a token chunk-extension value. At `maxChunkExtValueLength` the extension is complete, so it
must be within `maxChunkExtensions`, and only a byte that does not continue a token may follow.
-/
@[inline] private def chunkTokenByte (c : Config) (n exts : Nat) : Next :=
  if n + 1 < c.maxChunkExtValueLength then plain .chunkToken (n + 1) exts
  else if n + 1 == c.maxChunkExtValueLength && exts ≤ c.maxChunkExtensions then
    plain .chunkToken (n + 1) exts
  else stop

/-- The effect of byte `b` on a scan at `phase` with `n = count`. -/
@[inline]
private def next (c : Config) (phase : Phase) (n exts : Nat) (b : UInt8) : Next :=
  match phase with
  | .opaque => stop
  -- Request line
  | .reqLead =>
    if b == '\r'.toUInt8 then event .reqLeadCR 0
    else if isTchar b then plain .reqMethod 1
    else stop
  | .reqLeadCR => if b == '\n'.toUInt8 then event .reqLead 0 else stop
  | .reqMethod =>
    if isTchar b then
      if n + 1 ≤ maxMethodLength + c.maxStartLineLength then plain .reqMethod (n + 1) else stop
    else if b == ' '.toUInt8 then plain .reqTarget 0
    else stop
  | .reqTarget =>
    if isRequestTargetChar b then
      if n + 1 ≤ c.maxUriLength then plain .reqTarget (n + 1) else stop
    else if b == ' '.toUInt8 then event .reqVersion 0
    else stop
  | .reqVersion =>
    if n < 8 then
      if versionByte n b then plain .reqVersion (n + 1) else stop
    else if b == '\r'.toUInt8 then plain .opaque 0
    else stop
  -- Status line
  | .stVersion =>
    if n < 8 then
      if versionByte n b then plain .stVersion (n + 1) else stop
    else if b == ' '.toUInt8 then plain .stCode 0
    else stop
  | .stCode =>
    if n < 3 then
      if isDigitByte b then plain .stCode (n + 1) else stop
    else if b == ' '.toUInt8 then plain .stReason 0
    else if b == '\r'.toUInt8 then plain .opaque 0
    else stop
  | .stReason =>
    -- `parseReasonPhrase` skips bytes past `maxReasonPhraseLength`, so no length stops the scan.
    if isReasonPhraseByte b then plain .stReason n
    else if b == '\r'.toUInt8 then plain .opaque 0
    else stop
  -- Field line and obs-fold continuation
  | .fieldStart =>
    if isTchar b && 0 < c.maxHeaderNameLength then plain .fieldName 1 else stop
  | .fieldName =>
    if isTchar b then
      if n + 1 ≤ c.maxHeaderNameLength then plain .fieldName (n + 1) else stop
    else if b == ':'.toUInt8 then plain .fieldOws 0
    else stop
  | .fieldOws =>
    if isOwsByte b then
      if n + 1 ≤ c.maxSpaceSequence then plain .fieldOws (n + 1) else stop
    else if b == '\r'.toUInt8 then plain .opaque 0
    else if isFieldVChar b then fieldValueByte c 0
    else stop
  | .fieldValue =>
    if isFieldVChar b then fieldValueByte c n
    else if b == '\r'.toUInt8 then plain .opaque 0
    else stop
  | .fieldTrail =>
    if isOwsByte b then
      if n + 1 ≤ c.maxSpaceSequence then plain .fieldTrail (n + 1) else stop
    else if b == '\r'.toUInt8 then plain .opaque 0
    else stop
  -- Chunk-size line
  | .chunkZeros =>
    if b == '0'.toUInt8 then plain .chunkZeros (n + 1)
    else if isHexDigitByte b then plain .chunkDigits 1
    else if n == 0 then stop
    else chunkAfter c exts b
  | .chunkDigits =>
    if isHexDigitByte b then
      if n + 1 ≤ maxChunkSizeDigits then plain .chunkDigits (n + 1) else stop
    else chunkAfter c exts b
  | .chunkExtStart => chunkAfter c exts b
  | .chunkBws =>
    if isOwsByte b then chunkWs c .chunkBws n exts
    else if b == ';'.toUInt8 then semi c exts
    else stop
  | .chunkSemi =>
    if isOwsByte b then chunkWs c .chunkSemi n exts
    else if isTchar b && 0 < c.maxChunkExtNameLength then plain .chunkName 1 exts
    else stop
  | .chunkName =>
    if isTchar b then
      if n + 1 ≤ c.maxChunkExtNameLength then plain .chunkName (n + 1) exts else stop
    else if b == '='.toUInt8 then equals c exts
    else if isOwsByte b then chunkWs c .chunkNameWs 0 exts
    else if (b == ';'.toUInt8 || b == '\r'.toUInt8) && exts ≤ c.maxChunkExtensions then
      chunkAfter c exts b
    else stop
  | .chunkNameWs =>
    if isOwsByte b then chunkWs c .chunkNameWs n exts
    else if b == '='.toUInt8 then equals c exts
    else if b == ';'.toUInt8 && exts ≤ c.maxChunkExtensions then semi c exts
    else stop
  | .chunkEqWs =>
    if isOwsByte b then chunkWs c .chunkEqWs n exts
    else if b == '"'.toUInt8 then plain .chunkQuoted 0 exts
    else if isTchar b then chunkTokenByte c 0 exts
    else stop
  | .chunkToken =>
    if isTchar b then chunkTokenByte c n exts
    else if exts ≤ c.maxChunkExtensions then chunkAfter c exts b
    else stop
  | .chunkQuoted =>
    if b == '"'.toUInt8 then
      if exts ≤ c.maxChunkExtensions then plain .chunkExtStart 0 exts else stop
    else if b == '\\'.toUInt8 then plain .chunkEscape n exts
    else if isQdText b || b ≥ 0x80 then
      if n + 1 ≤ c.maxChunkExtValueLength then plain .chunkQuoted (n + 1) exts else stop
    else stop
  | .chunkEscape =>
    if quotedPairChar (Char.ofUInt8 b) || b ≥ 0x80 then
      if n + 1 ≤ c.maxChunkExtValueLength then plain .chunkQuoted (n + 1) exts else stop
    else stop

/--
Scans the unread bytes of `input` from `scan.scanned` on. Returns the scan and whether it stopped at
a byte that needs the parser, with `scanned` at that byte. With `pass`, the parser already returned
`.eof` on all of `input`, so the scan goes through every byte.
-/
def advance (c : Config) (pass : Bool) (scan : LineScan) (input : ByteArray.Iterator) :
    LineScan × Bool :=
  go input.array (input.idx + scan.scanned) scan.phase scan.count scan.exts
where
  go (arr : ByteArray) (j : Nat) (phase : Phase) (n exts : Nat) : LineScan × Bool :=
    if h : j < arr.size then
      let r := next c phase n exts arr[j]
      if r.plain || pass then go arr (j + 1) r.phase r.count r.exts
      else ({ scan with scanned := j - input.idx, phase, count := n, exts }, true)
    else
      ({ scan with scanned := j - input.idx, phase, count := n, exts }, false)
  termination_by arr.size - j

/--
Whether `scan` resumes for the line of `kind` at the start of `input`: it is an active scan of that
kind, more input may arrive (`final` is false), and the input is under `limit`. Otherwise the parser
runs on the line from its start, since its `.eof` then means an error or the scan is not this
line's.
-/
@[inline]
def resumes (scan : LineScan) (kind : LineKind) (final : Bool) (limit : Option Nat)
    (input : ByteArray.Iterator) : Bool :=
  scan.active && scan.kind == kind && !final && !(limit.any (input.remainingBytes ≥ ·))

/--
Whether a line is in progress: the parser returned `.eof` on it, so `scan` must be reset once it
parses or fails.
-/
@[inline]
def inProgress (scan : LineScan) : Bool :=
  scan.active || scan.tries != 0

/--
The scan to keep after the parser returned `.eof` on the line of `kind` at the start of `input`, read
from its start. The scan starts at the second such `.eof`.
-/
def afterEof (c : Config) (kind : LineKind) (scan : LineScan) (input : ByteArray.Iterator) :
    LineScan :=
  let tries := (if scan.kind == kind then scan.tries else 0) + 1
  if tries < 2 then { kind, tries }
  else ({ start kind with tries } |>.advance c true input).1

/--
Resumes `scan` (when `scan.resumes`) on the line at the start of `input`, running `parser` only if
the scan stops at a byte that needs it. Returns the scan to keep for the next read and the parser's
result, or `none` when the parser would return `.eof` and did not run.
-/
def resume (c : Config) (parser : Parser α) (scan : LineScan) (input : ByteArray.Iterator) :
    LineScan × Option (ParseResult α ByteArray.Iterator) :=
  match scan.advance c false input with
  | (scan, false) => (scan, none)
  | (scan, true) =>
    match parser input with
    | .error it .eof => ((scan.advance c true input).1, some (.error it .eof))
    | result => ({}, some result)

/--
Reads the line of `kind` at the start of `input` with `parser`, resuming `scan`. Returns the scan to
keep for the next read, and the parser's result, or `none` when the parser would return `.eof` and
did not run. On `none` the caller treats the line as a parser `.eof` with open input under `limit`.
A scan is inactive after the line parses or fails.

The machine inlines this combination of `resumes`, `resume` and `afterEof`, to leave its reader
untouched when a whole line is buffered.
-/
def read (c : Config) (kind : LineKind) (final : Bool) (limit : Option Nat) (parser : Parser α)
    (scan : LineScan) (input : ByteArray.Iterator) :
    LineScan × Option (ParseResult α ByteArray.Iterator) :=
  if scan.resumes kind final limit input then
    scan.resume c parser input
  else
    match parser input with
    | .error it .eof => (scan.afterEof c kind input, some (.error it .eof))
    | result => ({}, some result)

end LineScan

end Std.Http.Protocol.H1
