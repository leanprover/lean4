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
def Formatter.writeFloatAux [Writer ω m] [Monad m] (num : Float) : JsonT ω φ m Unit :=
  match JsonNumber.fromFloat? num with
  | .inl exceptional => JsonT.writeToBuffer (fun acc => Json.renderString exceptional acc)
  | .inr number => JsonT.write (toString number)

/--
Scalars are rendered exactly like `Lean.ToJson` renders them, so that both encoders can be used
against the same consumers. In particular 64 bit integers become decimal strings, as `bignumToJson`
does, because JavaScript cannot represent them exactly.
-/
instance : Formatter CompactFormatter where
  writeFloat val := Formatter.writeFloatAux val
  writeFloat32 val := Formatter.writeFloatAux val.toFloat
  writeString val := JsonT.writeToBuffer (fun acc => Json.renderString val acc)
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

namespace PrettyFormatter

variable [Writer ω m] [Monad m]

def writeIndent : JsonT ω PrettyFormatter m Unit := do
  let indent := (← JsonT.getFormatter).indent
  for _ in 0...(← JsonT.getFormatter).currentIndent do
    JsonT.write indent

@[inline]
def incIndent : JsonT ω PrettyFormatter m Unit :=
  JsonT.modifyFormatter fun f => { f with currentIndent := f.currentIndent + 1 }

@[inline]
def decIndent : JsonT ω PrettyFormatter m Unit :=
  JsonT.modifyFormatter fun f => { f with currentIndent := f.currentIndent - 1 }

@[inline]
def setHasValue (b : Bool) : JsonT ω PrettyFormatter m Unit :=
  JsonT.modifyFormatter fun f => { f with hasValue := b }

@[inline]
def getHasValue : JsonT ω PrettyFormatter m Bool :=
  return (← JsonT.getFormatter).hasValue

def beginArray : JsonT ω PrettyFormatter m Unit := do
  JsonT.write "["
  setHasValue false
  incIndent

def endArray : JsonT ω PrettyFormatter m Unit := do
  decIndent
  if ← getHasValue then
    JsonT.write "\n"
    writeIndent
  JsonT.write "]"

def beginArrayValue (first : Bool) : JsonT ω PrettyFormatter m Unit := do
  JsonT.write <| if first then "\n" else ",\n"
  writeIndent

def endArrayValue : JsonT ω PrettyFormatter m Unit := do
  setHasValue true

def beginObject : JsonT ω PrettyFormatter m Unit := do
  JsonT.write "{"
  setHasValue false
  incIndent

def endObject : JsonT ω PrettyFormatter m Unit := do
  decIndent
  if ← getHasValue then
    JsonT.write "\n"
    writeIndent
  JsonT.write "}"

def beginObjectKey (first : Bool) : JsonT ω PrettyFormatter m Unit := do
  JsonT.write <| if first then "\n" else ",\n"
  writeIndent

def endObjectKey : JsonT ω PrettyFormatter m Unit := do
  return ()

def beginObjectValue : JsonT ω PrettyFormatter m Unit := do
  JsonT.write ": "

def endObjectValue : JsonT ω PrettyFormatter m Unit := do
  setHasValue true

end PrettyFormatter

instance : Formatter PrettyFormatter where
  writeFloat val := Formatter.writeFloatAux val
  writeFloat32 val := Formatter.writeFloatAux val.toFloat
  writeString val := JsonT.writeToBuffer (fun acc => Json.renderString val acc)
  beginArray := PrettyFormatter.beginArray
  endArray := PrettyFormatter.endArray
  beginArrayValue first := PrettyFormatter.beginArrayValue first
  endArrayValue := PrettyFormatter.endArrayValue
  beginObject := PrettyFormatter.beginObject
  endObject := PrettyFormatter.endObject
  beginObjectKey first := PrettyFormatter.beginObjectKey first
  endObjectKey := PrettyFormatter.endObjectKey
  beginObjectValue := PrettyFormatter.beginObjectValue
  endObjectValue := PrettyFormatter.endObjectValue

end Std.Internal.Derse
