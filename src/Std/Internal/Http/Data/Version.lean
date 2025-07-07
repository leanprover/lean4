/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Init.Data

namespace Std
namespace Internal
namespace Http
namespace Data

/--
The 'Version' structure represents an HTTP version with a major and minor number. It includes
several standard versions of the HTTP protocol, such as HTTP/1.1, HTTP/2.0, and
HTTP/3.0.

* Reference: https://httpwg.org/specs/rfc9110.html#protocol.version
-/
inductive Version
  | v11
  | v20
  | v30
deriving Repr, Inhabited, BEq, DecidableEq

namespace Version

/--
Converts a pair of `Nat` to the corresponding `Version`.
-/
def fromNumber? : Nat → Nat → Option Version
  | 1, 1 => some .v11
  | 2, 0 => some .v20
  | 3, 0 => some .v30
  | _, _ => none

/--
Converts a `Version` to its corresponding major and minor numbers as a pair.
-/
def toNumber : Version → (Nat × Nat)
  | .v11 => (1, 1)
  | .v20 => (2, 0)
  | .v30 => (3, 0)

end Version
end Data
end Http
end Internal
end Std
