import Lean.Data.HashMap
open Lean

/--
A circuit node declaration. These are not recursive but instead contain indices into an `Env`.
-/
inductive Decl where
  /--
  A node with a constant output value.
  -/
  | const (b : Bool)
  /--
  An input node to the circuit.
  -/
  | atom (idx : Nat)
  /--
  An AIG gate with configurable input nodes and polarity. `l` and `r` are the
  input node indices while `linv` and `rinv` say whether there is an inverter on
  the left or right input.
  -/
  | gate (l r : Nat) (linv rinv : Bool)
  deriving BEq, Hashable, DecidableEq

/--
A cache that is valid with respect to some `Array Decl`.
-/
def Cache (_decls : Array Decl) := HashMap Decl Nat

/--
Lookup a `decl` in a `cache`.

If this returns `some i`, `Cache.find?_poperty` can be used to demonstrate: `decls[i] = decl`.
-/
@[irreducible]
def Cache.find? (cache : Cache decls) (decl : Decl) : Option Nat :=
  match cache.val.find? decl with
  | some hit =>
    if h1:hit < decls.size then
      if decls[hit]'h1 = decl then
        some hit
      else
        none
    else
      none
  | none => none

/--
This states that all indices, found in a `Cache` that is valid with respect to some `decls`,
are within bounds of `decls`.
-/
theorem Cache.find?_bounds {decls : Array Decl} {idx : Nat} (c : Cache decls) (decl : Decl)
    (h : c.find? decl = some idx) : idx < decls.size := by
  unfold find? at h
  split at h
  . split at h
    . split at h
      . injection h
        omega
      . contradiction
    . contradiction
  . contradiction

/--
This states that if `Cache.find? decl` returns `some i`, `decls[i] = decl`, holds.
-/
theorem Cache.find?_property {decls : Array Decl} {idx : Nat} (c : Cache decls) (decl : Decl)
    (h : c.find? decl = some idx) : decls[idx]'(Cache.find?_bounds c decl h) = decl := by
  unfold find? at h
  split at h
  . split at h
    . split at h
      . injection h
        subst idx; assumption
      . contradiction
    . contradiction
  . contradiction
