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
deriving Inhabited, Repr, BEq

namespace LineScan

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
        if b == ' '.toUInt8 && left < maxMethodLength then some (.run k .target config.maxUriLength)
        else none
      | .chunkLine, .token | .chunkLine, .zero | .chunkLine, .hexDigit =>
        if cr then some .opaque else none
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
Where a quoted string that starts at `i` ends within `bytes[i:stop]`.
-/
private inductive Quoted where
  /--
  The input ends inside the string, which has `length` characters.
  -/
  | inside (length : Nat)

  /--
  The string ends just before `next`.
  -/
  | closed (next : Nat)

  /--
  The input ends just after a backslash.
  -/
  | escaping

/--
Reads a quoted string's content from `i`, after its opening `"`.
-/
private def quoted (bytes : ByteArray) (i stop length : Nat) : Quoted :=
  if _ : i < stop then
    let b := byteAt bytes i
    if b == '"'.toUInt8 then .closed (i + 1)
    else if b == '\\'.toUInt8 then
      if i + 1 < stop then quoted bytes (i + 2) stop (length + 1) else .escaping
    else quoted bytes (i + 1) stop (length + 1)
  else
    .inside length
termination_by stop - i

/--
The chunk extensions from `i`: `*( BWS ";" BWS name [ BWS "=" BWS value ] )`. Each call reads one;
`fuel` bounds them.
-/
private def extensions (config : Config) (bytes : ByteArray) (i stop : Nat) : Nat → LineScan
  | 0 => .opaque
  | fuel + 1 =>
    let bws (start : Nat) := runOf .chunkLine .ows config.maxSpaceSequence (stop - start)
    let j := skip Class.ows.accepts bytes i stop
    if j == stop then bws i
    else if byteAt bytes j != ';'.toUInt8 then .opaque
    else
      let k := skip Class.ows.accepts bytes (j + 1) stop
      if k == stop then bws (j + 1)
      else
        let n := skip Class.token.accepts bytes k stop
        if n == stop then runOf .chunkLine .token config.maxChunkExtNameLength (stop - k)
        else
          let m := skip Class.ows.accepts bytes n stop
          if m == stop then bws n
          else if byteAt bytes m != '='.toUInt8 then extensions config bytes m stop fuel
          else
            let p := skip Class.ows.accepts bytes (m + 1) stop
            if p == stop then bws (m + 1)
            else if byteAt bytes p == '"'.toUInt8 then
              match quoted bytes (p + 1) stop 0 with
              | .inside length => runOf .chunkLine .quoted config.maxChunkExtValueLength length
              | .closed q => extensions config bytes q stop fuel
              | .escaping => .opaque
            else
              let v := skip Class.token.accepts bytes p stop
              if v == stop then runOf .chunkLine .token config.maxChunkExtValueLength (stop - p)
              else extensions config bytes v stop fuel

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
      if m == stop then runOf kind .token maxMethodLength (stop - i)
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
    let z := skip Class.zero.accepts bytes start stop
    let d := skip Class.hexDigit.accepts bytes z stop
    if d == stop then
      if d == z then .run kind .zero config.maxChunkLineLength
      else runOf kind .hexDigit maxChunkSizeDigits (d - z)
    else
      extensions config bytes d stop (config.maxChunkExtensions + 1)

end LineScan

end

end Std.Http.Protocol.H1
