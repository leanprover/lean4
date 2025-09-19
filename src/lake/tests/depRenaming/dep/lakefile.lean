import Lake
open System Lake DSL

package dep

target name : String := do
  return .pure <| (__name__).toString
