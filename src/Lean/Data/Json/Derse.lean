/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Internal.Derse.Se.Serializer.Json
public import Lean.Data.Json.Printer

public section

namespace Std.Internal.Derse

open Lean

/--
Renders `num` the way `Lean.Json` does: as a JSON number if it is finite and as one of the strings
`"NaN"`, `"Infinity"` and `"-Infinity"` otherwise, as JSON has no syntax for those values.
-/
@[inline]
def CompactFormatter.writeFloat [Writer ω m] [Monad m] (num : Float) : JsonT ω φ m Unit :=
  match JsonNumber.fromFloat? num with
  | .inl exceptional => JsonT.write (Json.renderString exceptional)
  | .inr number => JsonT.write (toString number)

/--
Scalars are rendered exactly like `Lean.ToJson` renders them, so that both encoders can be used
against the same consumers. In particular 64 bit integers become decimal strings, as `bignumToJson`
does, because JavaScript cannot represent them exactly.
-/
instance : Formatter CompactFormatter where
  writeNull := JsonT.write "null"
  writeBool val := JsonT.write (if val then "true" else "false")
  writeUInt8 val := JsonT.write (toString val)
  writeUInt16 val := JsonT.write (toString val)
  writeUInt32 val := JsonT.write (toString val)
  writeUInt64 val := JsonT.write (Json.renderString (toString val))
  writeInt8 val := JsonT.write (toString val)
  writeInt16 val := JsonT.write (toString val)
  writeInt32 val := JsonT.write (toString val)
  writeInt64 val := JsonT.write (Json.renderString (toString val))
  writeNat val := JsonT.write (toString val)
  writeInt val := JsonT.write (toString val)
  writeFloat val := CompactFormatter.writeFloat val
  writeFloat32 val := CompactFormatter.writeFloat val.toFloat
  writeString val := JsonT.write (Json.renderString val)
  beginArray := JsonT.write "["
  endArray := JsonT.write "]"
  beginArrayValue first := if first then pure () else JsonT.write ","
  endArrayValue := pure ()
  beginObject := JsonT.write "{"
  endObject := JsonT.write "}"
  beginObjectKey first := if first then pure () else JsonT.write ","
  endObjectKey := pure ()
  beginObjectValue := JsonT.write ":"
  endObjectValue := pure ()

end Std.Internal.Derse
