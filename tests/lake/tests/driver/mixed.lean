import Lake

open Lake DSL

package test where
  testDriver := "Test"
  testDrivers := #["Lib1", "exe1"]

lean_lib Test

lean_lib Lib1

lean_exe exe1 where
  root := `Main