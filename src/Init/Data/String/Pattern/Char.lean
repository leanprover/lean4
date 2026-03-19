/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Markus Himmel
-/
module

prelude
public import Init.Data.String.Pattern.Pred

set_option doc.verso true

/-!
This module defines the necessary instances to register {name}`Char` with the pattern framework.
-/

public section

namespace String.Slice.Pattern

namespace Char

instance {c : Char} : ForwardPattern c where
  skipPrefixOfNonempty? s h := ForwardPattern.skipPrefixOfNonempty? (· == c) s h
  skipPrefix? s := ForwardPattern.skipPrefix? (· == c) s
  startsWith s := ForwardPattern.startsWith (· == c) s

instance {c : Char} : StrictForwardPattern c where
  ne_startPos h q := StrictForwardPattern.ne_startPos (pat := (· == c)) h q

instance {c : Char} : LawfulForwardPattern c where
  skipPrefixOfNonempty?_eq h := LawfulForwardPattern.skipPrefixOfNonempty?_eq (pat := (· == c)) h
  startsWith_eq s := LawfulForwardPattern.startsWith_eq (pat := (· == c)) s

instance {c : Char} : ToForwardSearcher c (ToForwardSearcher.DefaultForwardSearcher (· == c)) where
  toSearcher s := ToForwardSearcher.toSearcher (· == c) s

instance {c : Char} : BackwardPattern c where
  dropSuffixOfNonempty? s h := BackwardPattern.dropSuffixOfNonempty? (· == c) s h
  dropSuffix? s := BackwardPattern.dropSuffix? (· == c) s
  endsWith s := BackwardPattern.endsWith (· == c) s

instance {c : Char} : StrictBackwardPattern c where
  ne_endPos h q := StrictBackwardPattern.ne_endPos (pat := (· == c)) h q

instance {c : Char} : LawfulBackwardPattern c where
  dropSuffixOfNonempty?_eq h := LawfulBackwardPattern.dropSuffixOfNonempty?_eq (pat := (· == c)) h
  endsWith_eq s := LawfulBackwardPattern.endsWith_eq (pat := (· == c)) s

instance {c : Char} : ToBackwardSearcher c (ToBackwardSearcher.DefaultBackwardSearcher c) :=
  .defaultImplementation

end Char

end String.Slice.Pattern
