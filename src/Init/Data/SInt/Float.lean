/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.Float.Float
public import Init.Data.SInt.Basic

public section

set_option linter.missingDocs true

/--
Truncates a floating-point number to the nearest 8-bit signed integer, rounding towards zero.

If the `Float` is larger than the maximum value for `Int8` (including `Inf`), returns the maximum value of
`Int8` (i.e. `Int8.maxValue`). If it is smaller than the minimum value for `Int8` (including `-Inf`),
returns the minimum value of `Int8` (i.e. `Int8.minValue`). If it is `NaN`, returns `0`.

This function has a logical model in terms of `Float.Model`.
-/
@[extern "lean_float_to_int8"] def Float.toInt8 : Float → Int8 :=
  fun a => a.toModel.toInt8
/--
Truncates a floating-point number to the nearest 16-bit signed integer, rounding towards zero.

If the `Float` is larger than the maximum value for `Int16` (including `Inf`), returns the maximum
value of `Int16` (i.e. `Int16.maxValue`). If it is smaller than the minimum value for `Int16`
(including `-Inf`), returns the minimum value of `Int16` (i.e. `Int16.minValue`). If it is `NaN`,
returns `0`.

This function has a logical model in terms of `Float.Model`.
-/
@[extern "lean_float_to_int16"] def Float.toInt16 : Float → Int16 :=
  fun a => a.toModel.toInt16
/--
Truncates a floating-point number to the nearest 32-bit signed integer, rounding towards zero.

If the `Float` is larger than the maximum value for `Int32` (including `Inf`), returns the maximum
value of `Int32` (i.e. `Int32.maxValue`). If it is smaller than the minimum value for `Int32`
(including `-Inf`), returns the minimum value of `Int32` (i.e. `Int32.minValue`). If it is `NaN`,
returns `0`.

This function has a logical model in terms of `Float.Model`.
-/
@[extern "lean_float_to_int32"] def Float.toInt32 : Float → Int32 :=
  fun a => a.toModel.toInt32
/--
Truncates a floating-point number to the nearest 64-bit signed integer, rounding towards zero.

If the `Float` is larger than the maximum value for `Int64` (including `Inf`), returns the maximum
value of `Int64` (i.e. `Int64.maxValue`). If it is smaller than the minimum value for `Int64`
(including `-Inf`), returns the minimum value of `Int64` (i.e. `Int64.minValue`). If it is `NaN`,
returns `0`.

This function has a logical model in terms of `Float.Model`.
-/
@[extern "lean_float_to_int64"] def Float.toInt64 : Float → Int64 :=
  fun a => a.toModel.toInt64
/--
Truncates a floating-point number to the nearest word-sized signed integer, rounding towards zero.

If the `Float` is larger than the maximum value for `ISize` (including `Inf`), returns the maximum
value of `ISize` (i.e. `ISize.maxValue`). If it is smaller than the minimum value for `ISize`
(including `-Inf`), returns the minimum value of `ISize` (i.e. `ISize.minValue`). If it is `NaN`,
returns `0`.

This function has a logical model in terms of `Float.Model`.
-/
@[extern "lean_float_to_isize"] def Float.toISize : Float → ISize :=
  fun a => a.toModel.toISize

/-- Obtains the `Float` whose value is the same as the given `Int8`. -/
@[extern "lean_int8_to_float"] def Int8.toFloat (n : Int8) : Float :=
  .ofModel (.ofInt8 n)
/-- Obtains the `Float` whose value is the same as the given `Int16`. -/
@[extern "lean_int16_to_float"] def Int16.toFloat (n : Int16) : Float :=
  .ofModel (.ofInt16 n)
/-- Obtains the `Float` whose value is the same as the given `Int32`. -/
@[extern "lean_int32_to_float"] def Int32.toFloat (n : Int32) : Float :=
  .ofModel (.ofInt32 n)
/--
Obtains a `Float` whose value is near the given `Int64`.

It will be exactly the value of the given `Int64` if such a `Float` exists. If no such `Float`
exists, the returned value will either be the smallest `Float` that is larger than the given value,
or the largest `Float` that is smaller than the given value.

This function has a logical model in terms of `Float.Model`, but is overridden at runtime with an
efficient implementation.
-/
@[extern "lean_int64_to_float"] def Int64.toFloat (n : Int64) : Float :=
  .ofModel (.ofInt64 n)
/--
Obtains a `Float` whose value is near the given `ISize`.

It will be exactly the value of the given `ISize` if such a `Float` exists. If no such `Float`
exists, the returned value will either be the smallest `Float` that is larger than the given value,
or the largest `Float` that is smaller than the given value.

This function has a logical model in terms of `Float.Model`, but is overridden at runtime with an
efficient implementation.
-/
@[extern "lean_isize_to_float"] def ISize.toFloat (n : ISize) : Float :=
  .ofModel (.ofISize n)
