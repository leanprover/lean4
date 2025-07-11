/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Init

namespace Std
namespace Http
namespace Data

set_option linter.all true

/--
The 'Version' structure represents an HTTP version with a major and minor number. It includes
several standard versions of the HTTP protocol, such as HTTP/1.1, HTTP/2.0, and
HTTP/3.0.

* Reference: https://httpwg.org/specs/rfc9110.html#protocol.version
-/
inductive Version

  /--
  `HTTP/1.1`
  -/
  | v11

  /--
  `HTTP/2.0`
  -/
  | v20

  /--
  `HTTP/3.0`
  -/
  | v30

deriving Repr, Inhabited, BEq, DecidableEq

instance : ToString Version where
  toString
    | .v11 => "HTTP/1.1"
    | .v20 => "HTTP/2.0"
    | .v30 => "HTTP/3.0"

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
Converts `String` to the corresponding `Version`.
-/
def fromString? : String → Option Version
  | "HTTP/1.1" => some .v11
  | "HTTP/2.0" => some .v20
  | "HTTP/3.0" => some .v30
  | _ => none

/--
Converts a `Version` to its corresponding major and minor numbers as a pair.
-/
def toNumber : Version → (Nat × Nat)
  | .v11 => (1, 1)
  | .v20 => (2, 0)
  | .v30 => (3, 0)
