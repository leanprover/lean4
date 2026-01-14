import Lake
open System Lake DSL

package test

def depVer : String := get_config? depVer |>.getD ""

require "Seasawher" / "mdgen" @ depVer
