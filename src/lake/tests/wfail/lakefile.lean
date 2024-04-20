import Lake
open Lake DSL

package test

target warn : PUnit := Job.async do
  logWarning "foo"
  return ((), .nil)
