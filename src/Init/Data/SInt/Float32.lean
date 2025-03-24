/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Init.Data.Float32
import Init.Data.SInt.Basic

set_option linter.missingDocs true

/--
Truncates the value to the nearest integer, rounding towards zero.
If NaN, returns `0`.
If larger than the maximum value for `Int8` (including Inf), returns the maximum value of `Int8`
(i.e. `Int8.maxValue`).
If smaller than the minimum value for `Int8` (including -Inf), returns the minimum value of `Int8`
(i.e. `Int8.minValue`).
-/
@[extern "lean_float32_to_int8"] opaque Float32.toInt8 : Float32 → Int8
/--
Truncates the value to the nearest integer, rounding towards zero.
If NaN, returns `0`.
If larger than the maximum value for `Int16` (including Inf), returns the maximum value of `Int16`
(i.e. `Int16.maxValue`).
If smaller than the minimum value for `Int16` (including -Inf), returns the minimum value of `Int16`
(i.e. `Int16.minValue`).
-/
@[extern "lean_float32_to_int16"] opaque Float32.toInt16 : Float32 → Int16
/--
Truncates the value to the nearest integer, rounding towards zero.
If NaN, returns `0`.
If larger than the maximum value for `Int32` (including Inf), returns the maximum value of `Int32`
(i.e. `Int32.maxValue`).
If smaller than the minimum value for `Int32` (including -Inf), returns the minimum value of `Int32`
(i.e. `Int32.minValue`).
-/
@[extern "lean_float32_to_int32"] opaque Float32.toInt32 : Float32 → Int32
/--
Truncates the value to the nearest integer, rounding towards zero.
If NaN, returns `0`.
If larger than the maximum value for `Int64` (including Inf), returns the maximum value of `Int64`
(i.e. `Int64.maxValue`).
If smaller than the minimum value for `Int64` (including -Inf), returns the minimum value of `Int64`
(i.e. `Int64.minValue`).
-/
@[extern "lean_float32_to_int64"] opaque Float32.toInt64 : Float32 → Int64
/--
Truncates the value to the nearest integer, rounding towards zero.
If NaN, returns `0`.
If larger than the maximum value for `ISize` (including Inf), returns the maximum value of `ISize`
(i.e. `ISize.maxValue`).
If smaller than the minimum value for `ISize` (including -Inf), returns the minimum value of `ISize`
(i.e. `ISize.minValue`).
-/
@[extern "lean_float32_to_isize"] opaque Float32.toISize : Float32 → ISize

/-- Obtains the `Float32` whose value is the same as the given `Int8`. -/
@[extern "lean_int8_to_float32"] opaque Int8.toFloat32 (n : Int8) : Float32
/-- Obtains the `Float32` whose value is the same as the given `Int16`. -/
@[extern "lean_int16_to_float32"] opaque Int16.toFloat32 (n : Int16) : Float32
/--
Obtains a `Float32` whose value is near the given `Int32`.

It will be exactly the value of the given `Int32` if such a `Float32` exists. If no such `Float32`
exists, the returned value will either be the smallest `Float32` that is larger than the given
value, or the largest `Float32` that is smaller than the given value.
-/
@[extern "lean_int32_to_float32"] opaque Int32.toFloat32 (n : Int32) : Float32
/--
Obtains a `Float32` whose value is near the given `Int64`.

It will be exactly the value of the given `Int64` if such a `Float32` exists. If no such `Float32`
exists, the returned value will either be the smallest `Float32` that is larger than the given
value, or the largest `Float32` that is smaller than the given value.
-/
@[extern "lean_int64_to_float32"] opaque Int64.toFloat32 (n : Int64) : Float32
/--
Obtains a `Float32` whose value is near the given `ISize`.

It will be exactly the value of the given `ISize` if such a `Float32` exists. If no such `Float32`
exists, the returned value will either be the smallest `Float32` that is larger than the given
value, or the largest `Float32` that is smaller than the given value.
-/
@[extern "lean_isize_to_float32"] opaque ISize.toFloat32 (n : ISize) : Float32
