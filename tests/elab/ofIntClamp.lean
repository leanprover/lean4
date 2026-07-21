module

/-!
Tests for the `IntX.ofIntClamp` functions, which construct a signed integer from an
`Int`, clamping out-of-range values to the minimum/maximum representable value.
-/

-- In-range values are preserved.
#guard Int8.ofIntClamp 5 = 5
#guard Int16.ofIntClamp 5 = 5
#guard Int32.ofIntClamp 5 = 5
#guard Int64.ofIntClamp 5 = 5
#guard ISize.ofIntClamp 5 = 5

#guard Int8.ofIntClamp (-5) = -5
#guard Int16.ofIntClamp (-5) = -5
#guard Int32.ofIntClamp (-5) = -5
#guard Int64.ofIntClamp (-5) = -5
#guard ISize.ofIntClamp (-5) = -5

-- The boundary values themselves are preserved.
#guard Int8.ofIntClamp Int8.maxValue.toInt = Int8.maxValue
#guard Int8.ofIntClamp Int8.minValue.toInt = Int8.minValue
#guard Int16.ofIntClamp Int16.maxValue.toInt = Int16.maxValue
#guard Int16.ofIntClamp Int16.minValue.toInt = Int16.minValue
#guard Int32.ofIntClamp Int32.maxValue.toInt = Int32.maxValue
#guard Int32.ofIntClamp Int32.minValue.toInt = Int32.minValue
#guard Int64.ofIntClamp Int64.maxValue.toInt = Int64.maxValue
#guard Int64.ofIntClamp Int64.minValue.toInt = Int64.minValue
#guard ISize.ofIntClamp ISize.maxValue.toInt = ISize.maxValue
#guard ISize.ofIntClamp ISize.minValue.toInt = ISize.minValue

-- Values above the maximum clamp to the maximum.
#guard Int8.ofIntClamp 128 = Int8.maxValue
#guard Int8.ofIntClamp 1000 = Int8.maxValue
#guard Int16.ofIntClamp 32768 = Int16.maxValue
#guard Int32.ofIntClamp 2147483648 = Int32.maxValue
#guard Int64.ofIntClamp 9223372036854775808 = Int64.maxValue
#guard ISize.ofIntClamp (ISize.maxValue.toInt + 1) = ISize.maxValue

-- Values below the minimum clamp to the minimum.
#guard Int8.ofIntClamp (-129) = Int8.minValue
#guard Int8.ofIntClamp (-1000) = Int8.minValue
#guard Int16.ofIntClamp (-32769) = Int16.minValue
#guard Int32.ofIntClamp (-2147483649) = Int32.minValue
#guard Int64.ofIntClamp (-9223372036854775809) = Int64.minValue
#guard ISize.ofIntClamp (ISize.minValue.toInt - 1) = ISize.minValue
