/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Internal.Char
public import Std.Http.Protocol.H1.Config

/-!
Checks for a line that arrives in pieces. When the parser runs out of input inside a line,
`LineScan.classify` notes the run of bytes the line ends in and how much longer that run may grow
within its limit. For the bytes that arrive next, `LineScan.extend` decides whether they continue
that run. If they do, the parser would again run out of input, so the reader skips it. Any other byte
(one that may end the line, fail it, start its next part, or pass a limit) makes the reader parse the
line again. A line that arrives one byte per read therefore costs time linear in its length, and a
byte that fails the line still fails it as soon as it arrives.
-/

namespace Std.Http.Protocol.H1

open Internal.Char

public section

set_option linter.all true

/--
The longest method token the parser reads.
-/
def maxMethodLength : Nat := 64

/--
The most significant hex digits a chunk size may have.
-/
def maxChunkSizeDigits : Nat := 16

/--
The kinds of line the reader parses as one item.
-/
inductive LineKind where
  /--
  A request line, with any empty lines before it.
  -/
  | requestLine

  /--
  A status line.
  -/
  | statusLine

  /--
  A field line of a header or trailer section, or the empty line that ends the section.
  -/
  | fieldLine

  /--
  A line that continues a field value after an obs-fold.
  -/
  | foldLine

  /--
  A chunk-size line with its extensions.
  -/
  | chunkLine
deriving Inhabited, Repr, BEq

/--
A class of bytes that can extend a run of a line.
-/
inductive LineScan.Class where
  /--
  `tchar`: a method, field name, or chunk-extension name or value.
  -/
  | token

  /--
  A request-target byte (`isRequestTargetChar`).
  -/
  | target

  /--
  `field-content` bytes: a field value or a reason phrase.
  -/
  | fieldContent

  /--
  `OWS`.
  -/
  | ows

  /--
  `0`: the leading zeros of a chunk size.
  -/
  | zero

  /--
  A hex digit of a chunk size.
  -/
  | hexDigit

  /--
  A byte of a quoted chunk-extension value other than `"` and `\`.
  -/
  | quoted
deriving Inhabited, Repr, BEq

/--
Whether `b` is in the class.
-/
@[inline]
def LineScan.Class.accepts : LineScan.Class → UInt8 → Bool
  | .token, b => tchar (Char.ofUInt8 b)
  | .target, b => isRequestTargetChar b
  | .fieldContent, b => Internal.Char.fieldContent (Char.ofUInt8 b)
  | .ows, b => Internal.Char.ows (Char.ofUInt8 b)
  | .zero, b => b == '0'.toUInt8
  | .hexDigit, b => isHexDigitByte b
  | .quoted, b => qdtext (Char.ofUInt8 b) || b ≥ 0x80

/--
The part of a chunk-size line (`chunk-size [ chunk-ext ]`) that its last byte belongs to.
-/
inductive LineScan.ChunkPart where
  /--
  The leading zeros of the chunk size.
  -/
  | zeros

  /--
  The significant hex digits of the chunk size.
  -/
  | digits

  /--
  `BWS` that must be followed by `;`: after the chunk size or an extension's value.
  -/
  | sep

  /--
  `BWS` after a `;`.
  -/
  | semi

  /--
  An extension name.
  -/
  | name

  /--
  `BWS` after an extension name, which only `=` or the next `;` may follow.
  -/
  | nameOws

  /--
  `BWS` after a `=`.
  -/
  | eq

  /--
  An unquoted extension value.
  -/
  | value

  /--
  A quoted extension value.
  -/
  | quoted

  /--
  A quoted extension value, just after a backslash.
  -/
  | escape
deriving Inhabited, Repr, BEq

/--
Which bytes may follow the part of a line read so far without the parser having to see them.
-/
inductive LineScan where
  /--
  The parser has to see the next byte.
  -/
  | opaque

  /--
  The line of kind `kind` ends inside a run of `cls` bytes, which may grow by `left` more.
  -/
  | run (kind : LineKind) (cls : LineScan.Class) (left : Nat)

  /--
  The line of kind `kind` has read `pos` bytes of its fixed-format part: `HTTP/d.d` after a
  request-target, or `HTTP/d.d SP ddd` at the start of a status line.
  -/
  | fixed (kind : LineKind) (pos : Nat)

  /--
  A chunk-size line ends in part `part`, which holds `n` bytes (zeros, digits, whitespace, or the
  characters of a name or value so far), after `count` extensions were started.
  -/
  | chunk (part : LineScan.ChunkPart) (n count : Nat)
deriving Inhabited, Repr, BEq

namespace LineScan

/--
The scan of a chunk-size line after one more byte `b`, mirroring `parseChunkSize`; `none` when the
parser has to see `b`. An extension is counted against `maxChunkExtensions` where the parser counts
it: at the byte after it, at the `"` that closes its quoted value, or when its unquoted value reaches
its limit. Past the limit, those bytes go to the parser.
-/
@[inline]
private def chunkStep (config : Config) (part : ChunkPart) (n count : Nat) (b : UInt8) :
    Option LineScan :=
  let cr := b == '\r'.toUInt8
  let semi := b == ';'.toUInt8
  let ows := Class.ows.accepts b
  let tok := Class.token.accepts b
  let space := config.maxSpaceSequence
  let maxValue := config.maxChunkExtValueLength
  let counted := count ≤ config.maxChunkExtensions
  -- The byte after the chunk size or a value: the end of the line, a `;`, or `BWS` before a `;`.
  let next : Option LineScan :=
    if cr then some .opaque
    else if semi then some (.chunk .semi 0 (count + 1))
    else if ows && 0 < space then some (.chunk .sep 1 count)
    else none
  match part with
  | .zeros =>
    if b == '0'.toUInt8 then some (.chunk .zeros (n + 1) count)
    else if Class.hexDigit.accepts b then some (.chunk .digits 1 count)
    else if n == 0 then none
    else next
  | .digits =>
    if Class.hexDigit.accepts b then
      if n < maxChunkSizeDigits then some (.chunk .digits (n + 1) count) else none
    else next
  | .sep =>
    if ows then (if n < space then some (.chunk .sep (n + 1) count) else none)
    else if semi then some (.chunk .semi 0 (count + 1))
    else if cr && n == 0 then some .opaque
    else none
  | .semi =>
    if ows then (if n < space then some (.chunk .semi (n + 1) count) else none)
    else if tok && 0 < config.maxChunkExtNameLength then some (.chunk .name 1 count)
    else none
  | .name =>
    if tok then (if n < config.maxChunkExtNameLength then some (.chunk .name (n + 1) count) else none)
    else if ows then (if 0 < space then some (.chunk .nameOws 1 count) else none)
    else if b == '='.toUInt8 then some (.chunk .eq 0 count)
    else if (semi || cr) && counted then next
    else none
  | .nameOws =>
    -- Whitespace after a name leads to `=` or to the next `;`, never to the end of the line.
    if ows then (if n < space then some (.chunk .nameOws (n + 1) count) else none)
    else if b == '='.toUInt8 then some (.chunk .eq 0 count)
    else if semi && counted then next
    else none
  | .eq =>
    if ows then (if n < space then some (.chunk .eq (n + 1) count) else none)
    else if b == '"'.toUInt8 then some (.chunk .quoted 0 count)
    else if tok && (1 < maxValue || (1 == maxValue && counted)) then some (.chunk .value 1 count)
    else none
  | .value =>
    if tok then
      if n + 1 < maxValue || (n + 1 == maxValue && counted) then some (.chunk .value (n + 1) count)
      else none
    else if counted then next
    else none
  | .quoted =>
    if b == '"'.toUInt8 then (if counted then some (.chunk .sep 0 count) else none)
    else if b == '\\'.toUInt8 then some (.chunk .escape n count)
    else if Class.quoted.accepts b && n < maxValue then some (.chunk .quoted (n + 1) count)
    else none
  | .escape =>
    if (quotedPairChar (Char.ofUInt8 b) || b ≥ 0x80) && n < maxValue then
      some (.chunk .quoted (n + 1) count)
    else none

/--
The scan after one more byte `b` of a line of kind `kind`, when the parser would again run out of
input; `none` when it has to see `b`. Besides growing a run, `b` may start the next part of a line
where the parser checks nothing at that point: the `:` after a field name, the first byte of a field
value, the SP after a method, or the CR that ends a field value, reason phrase, chunk size or
extension token, after which only the parser may read on.
-/
@[inline]
private def step (config : Config) (kind : LineKind) : LineScan → UInt8 → Option LineScan
  | .opaque, _ => none
  | .chunk part n count, b => if kind == .chunkLine then chunkStep config part n count b else none
  | .fixed k pos, b =>
    let isDigit := b ≥ '0'.toUInt8 && b ≤ '9'.toUInt8
    -- `HTTP/d.d`: the name, a digit, a dot and a digit.
    let version : Bool := match pos with
      | 0 => b == 'H'.toUInt8 | 1 | 2 => b == 'T'.toUInt8 | 3 => b == 'P'.toUInt8
      | 4 => b == '/'.toUInt8 | 6 => b == '.'.toUInt8 | _ => isDigit
    if k != kind then none
    else if pos < 8 then (if version then some (.fixed k (pos + 1)) else none)
    else match k with
      | .requestLine => if pos == 8 && b == '\r'.toUInt8 then some .opaque else none
      | .statusLine =>
        if pos == 8 then (if b == ' '.toUInt8 then some (.fixed k 9) else none)
        else if pos < 12 then (if isDigit then some (.fixed k (pos + 1)) else none)
        else if b == ' '.toUInt8 then some (.run k .fieldContent config.maxReasonPhraseLength)
        else if b == '\r'.toUInt8 then some .opaque
        else none
      | _ => none
  | .run k cls left, b =>
    if k != kind then none
    else if left > 0 && cls.accepts b then some (.run k cls (left - 1))
    else
      let cr := b == '\r'.toUInt8
      match k, cls with
      | .fieldLine, .token =>
        if b == ':'.toUInt8 && left < config.maxHeaderNameLength then
          some (.run k .ows config.maxSpaceSequence)
        else none
      | .fieldLine, .ows | .foldLine, .ows =>
        if cr then some .opaque
        else if Class.fieldContent.accepts b && !Class.ows.accepts b && 0 < config.maxHeaderValueLength then
          some (.run k .fieldContent (config.maxHeaderValueLength - 1))
        else none
      | .fieldLine, .fieldContent | .foldLine, .fieldContent | .statusLine, .fieldContent =>
        if cr then some .opaque else none
      | .requestLine, .token =>
        if b == ' '.toUInt8 && left < maxMethodLength + config.maxStartLineLength then
          some (.run k .target config.maxUriLength)
        else none
      | _, _ => none

/--
For the bytes `bytes[start:stop]` that arrived after a line of kind `kind` with this scan, the scan
of the longer line when the parser would again run out of input (`step`), and `none` when it has to
see them.
-/
def extend (scan : LineScan) (kind : LineKind) (config : Config) (bytes : ByteArray)
    (start stop : Nat) : Option LineScan :=
  go scan start
where
  go (scan : LineScan) (i : Nat) : Option LineScan :=
    if _ : i < stop then
      if h : i < bytes.size then
        match step config kind scan bytes[i] with
        | some scan => go scan (i + 1)
        | none => none
      else
        none
    else
      some scan
  termination_by stop - i

/--
The byte at `i`, or `0`, which no run accepts and no structure byte matches, past the end.
-/
@[inline]
private def byteAt (bytes : ByteArray) (i : Nat) : UInt8 :=
  bytes[i]?.getD 0

/--
The first index from `i` below `stop` whose byte does not satisfy `p`, or `stop`.
-/
@[specialize]
private def skip (p : UInt8 → Bool) (bytes : ByteArray) (i stop : Nat) : Nat :=
  if _ : i < stop then
    if h : i < bytes.size then (if p bytes[i] then skip p bytes (i + 1) stop else i) else i
  else
    stop
termination_by stop - i

/--
A run of `cls` that already holds `length` bytes of the `limit` it may reach.
-/
@[inline]
private def runOf (kind : LineKind) (cls : LineScan.Class) (limit length : Nat) : LineScan :=
  if length ≤ limit then .run kind cls (limit - length) else .opaque

/--
The rest of a field line from `i`, just after its `:`, or of a fold line from its start: whitespace,
then the value.
-/
private def fieldValue (kind : LineKind) (config : Config) (bytes : ByteArray) (i stop : Nat) :
    LineScan :=
  let v := skip Class.ows.accepts bytes i stop
  if v == stop then
    runOf kind .ows config.maxSpaceSequence (stop - i)
  else if skip Class.fieldContent.accepts bytes v stop == stop then
    runOf kind .fieldContent config.maxHeaderValueLength (stop - v)
  else
    .opaque

/--
The end of the empty lines (`CRLF`) from `i` that may come before a request line.
-/
private def emptyLines (bytes : ByteArray) (i stop : Nat) : Nat :=
  if _ : i + 1 < stop then
    if byteAt bytes i == '\r'.toUInt8 && byteAt bytes (i + 1) == '\n'.toUInt8 then
      emptyLines bytes (i + 2) stop
    else
      i
  else
    i
termination_by stop - i

/--
The scan of the line `bytes[start:stop]` of kind `kind`, which its parser read to the end without
completing it or finding it malformed.
-/
def classify (kind : LineKind) (config : Config) (bytes : ByteArray) (start stop : Nat) :
    LineScan :=
  match kind with
  | .requestLine =>
    let i := emptyLines bytes start stop
    if i < stop && (byteAt bytes i == '\r'.toUInt8 || byteAt bytes i == '\n'.toUInt8) then .opaque
    else
      let m := skip Class.token.accepts bytes i stop
      -- `parseMethod` skips a method past `maxMethodLength` for up to `maxStartLineLength` bytes.
      if m == stop then runOf kind .token (maxMethodLength + config.maxStartLineLength) (stop - i)
      else if byteAt bytes m != ' '.toUInt8 then .opaque
      else
        let t := skip Class.target.accepts bytes (m + 1) stop
        if t == stop then runOf kind .target config.maxUriLength (stop - (m + 1))
        else if byteAt bytes t == ' '.toUInt8 && stop - (t + 1) ≤ 8 then .fixed kind (stop - (t + 1))
        else .opaque
  | .statusLine =>
    -- `HTTP/d.d SP ddd` takes 12 bytes, and an SP and the reason phrase may follow.
    let r := start + 13
    if stop - start ≤ 12 then .fixed kind (stop - start)
    else if byteAt bytes (start + 12) == ' '.toUInt8 &&
        skip Class.fieldContent.accepts bytes r stop == stop then
      runOf kind .fieldContent config.maxReasonPhraseLength (stop - r)
    else
      .opaque
  | .fieldLine =>
    let first := byteAt bytes start
    if first == '\r'.toUInt8 || first == '\n'.toUInt8 then .opaque
    else
      let n := skip Class.token.accepts bytes start stop
      if n == stop then runOf kind .token config.maxHeaderNameLength (stop - start)
      else if byteAt bytes n == ':'.toUInt8 then fieldValue kind config bytes (n + 1) stop
      else .opaque
  | .foldLine =>
    fieldValue kind config bytes start stop
  | .chunkLine =>
    -- The same transitions `extend` takes, so a line scanned in pieces gets the same scan.
    ((LineScan.chunk .zeros 0 0).extend kind config bytes start stop).getD .opaque

end LineScan

end

end Std.Http.Protocol.H1
