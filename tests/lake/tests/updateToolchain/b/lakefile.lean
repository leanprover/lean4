import Lake
open System Lake DSL

def fixedToolchain : Bool :=
   get_config? fixedToolchain |>.bind envToBool? |>.getD false

package b where
  fixedToolchain := fixedToolchain
