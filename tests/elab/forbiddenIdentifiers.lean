import Lean
/-!
`withForbidden` stops a term at a non-reserved word used as a bare identifier, while the word
stays usable as an identifier (escaped, projected, or a plain declaration name).
-/
open Lean Elab Command Parser

namespace ForbiddenIdentTest

-- `#collect e sep e'` parses `e` with the non-reserved word `sep` forbidden, so a bare `sep`
-- ends `e` without `sep` being a reserved keyword.
@[command_parser]
def collectCmd : Parser := leading_parser
  "#collect " >> withForbidden "sep" termParser >> nonReservedSymbol "sep" >> ppSpace >> termParser

@[command_elab collectCmd]
def elabCollect : CommandElab := fun _ => pure ()

-- A bare `sep` ends the first term (requires the forbidding; else `a sep` is an application).
#collect a sep b
-- A multi-token first term still stops at the bare `sep`.
#collect f a sep b
-- Escaped `«sep»` is not forbidden: it is consumed as the first term.
#collect «sep» sep b
-- A projection `.sep` (rawIdent path) is not forbidden.
#collect (id x).sep sep b
-- The word remains usable as an ordinary identifier.
def sep : Nat := 0

end ForbiddenIdentTest
