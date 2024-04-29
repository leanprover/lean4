import Lake
open Lake DSL

package test

lean_lib Warn

target warn : PUnit := Job.async do
  logWarning "foo"
  return ((), .nil)
