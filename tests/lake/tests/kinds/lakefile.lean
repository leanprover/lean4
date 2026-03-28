import Lake
open System Lake DSL

package test where
  srcDir := "files"

lean_lib Lib
lean_exe exe

input_file inFile where
  path := "files" / "test.txt"

input_dir inDir where
  path := "files"

target pathTarget : FilePath :=
  return Job.pure "files"

target dynlibTarget : Dynlib :=
  return Job.pure {name := "test", path := "test.lib"}
