import Lean.Data.Xml
open Lean.Xml

/-! Test XML parsing. -/

/-! Test whether trailing whitespace in opening tags is handled correctly. -/
#eval parse "<a ><b a=\"v\" ></b></a>"

/-! Test whether comments are parsed correctly. -/
#eval parse "<a><!-- comment --></a>"
