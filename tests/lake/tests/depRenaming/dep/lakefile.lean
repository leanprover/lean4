import Lake
open System Lake DSL

package dep

target name : String := Job.sync do
  return  (__name__).getPrefix.toString
