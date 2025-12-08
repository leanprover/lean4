/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Grove.Framework

open Grove.Framework Widget

namespace GroveStdlib.Std.CoreTypesAndOperations

namespace StringsAndFormatting

def highLevelStringTypes : List Lean.Name :=
  [`String, `String.Slice, `String.Pos, `String.Slice.Pos]

def sliceProducing : AssociationTable (β := Alias Lean.Name) .declaration
    [`String, `String.Slice,
     Alias.mk `String.Pos "string-pos-forwards" "String.Pos (forwards)",
     Alias.mk `String.Pos "string-pos-backwards" "String.Pos (backwards)",
     Alias.mk `String.Pos "string-pos-noproof" "String.Pos (no proof)",
     Alias.mk `String.Slice.Pos "string-slice-pos-forwards" "String.Slice.Pos (forwards)",
     Alias.mk `String.Slice.Pos "string-slice-pos-backwards" "String.Slice.Pos (backwards)",
     Alias.mk `String.Slice.Pos "string-slice-pos-noproof" "String.Slice.Pos (no proof)"] where
  id := "slice-producing"
  title := "String functions returning slices"
  description := "Operations on strings and string slices that themselves return a new string slice."
  dataSources n := DataSource.definitionsInNamespace n.inner

end StringsAndFormatting

open StringsAndFormatting

def stringsAndFormatting : Node :=
  .section "strings-and-formatting" "Strings and formatting"
    #[.associationTable sliceProducing]

end GroveStdlib.Std.CoreTypesAndOperations
