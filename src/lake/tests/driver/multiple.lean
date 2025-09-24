import Lake

open Lake DSL

package test where
  testDrivers := #["Lib1", "Lib2"]

lean_lib Lib1

lean_lib Lib2