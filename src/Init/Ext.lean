/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Mario Carneiro
-/
prelude
import Init.Data.ToString.Macro
import Init.TacticsExtra
import Init.RCases

namespace Lean
namespace Parser.Attr

/--
The flag `(iff := false)` prevents `ext` from generating an `ext_iff` lemma.
-/
syntax extIff := atomic("(" &"iff" " := " &"false" ")")

/--
The flag `(flat := false)` causes `ext` to not flatten parents' fields when generating an `ext` lemma.
-/
syntax extFlat := atomic("(" &"flat" " := " &"false" ")")

/--
Registers an extensionality theorem.

* When `@[ext]` is applied to a theorem, the theorem is registered for the `ext` tactic, and it generates an "`ext_iff`" theorem.
  The name of the theorem is from adding the suffix `_iff` to the theorem name.

* When `@[ext]` is applied to a structure, it generates an `.ext` theorem and applies the `@[ext]` attribute to it.
  The result is an `.ext` and an `.ext_iff` theorem with the `.ext` theorem registered for the `ext` tactic.

* An optional natural number argument, e.g. `@[ext 9000]`, specifies a priority for the `ext` lemma.
  Higher-priority lemmas are chosen first, and the default is `1000`.

* The flag `@[ext (iff := false)]` disables generating an `ext_iff` theorem.

* The flag `@[ext (flat := false)]` causes generated structure extensionality theorems to show inherited fields based on their representation,
  rather than flattening the parents' fields into the lemma's equality hypotheses.
-/
syntax (name := ext) "ext" (ppSpace extIff)? (ppSpace extFlat)? (ppSpace prio)? : attr
end Parser.Attr

-- TODO: rename this namespace?
namespace Elab.Tactic.Ext

/--
Applies extensionality lemmas that are registered with the `@[ext]` attribute.
* `ext pat*` applies extensionality theorems as much as possible,
  using the patterns `pat*` to introduce the variables in extensionality theorems using `rintro`.
  For example, the patterns are used to name the variables introduced by lemmas such as `funext`.
* Without patterns,`ext` applies extensionality lemmas as much
  as possible but introduces anonymous hypotheses whenever needed.
* `ext pat* : n` applies ext theorems only up to depth `n`.

The `ext1 pat*` tactic is like `ext pat*` except that it only applies a single extensionality theorem.

Unused patterns will generate warning.
Patterns that don't match the variables will typically result in the introduction of anonymous hypotheses.
-/
syntax (name := ext) "ext" (colGt ppSpace rintroPat)* (" : " num)? : tactic

/-- Apply a single extensionality theorem to the current goal. -/
syntax (name := applyExtTheorem) "apply_ext_theorem" : tactic

/--
`ext1 pat*` is like `ext pat*` except that it only applies a single extensionality theorem rather
than recursively applying as many extensionality theorems as possible.

The `pat*` patterns are processed using the `rintro` tactic.
If no patterns are supplied, then variables are introduced anonymously using the `intros` tactic.
-/
macro "ext1" xs:(colGt ppSpace rintroPat)* : tactic =>
  if xs.isEmpty then `(tactic| apply_ext_theorem <;> intros)
  else `(tactic| apply_ext_theorem <;> rintro $xs*)

end Elab.Tactic.Ext
end Lean

attribute [ext] Prod PProd Sigma PSigma
attribute [ext] funext propext Subtype.eq Array.ext

@[ext] protected theorem PUnit.ext (x y : PUnit) : x = y := rfl
protected theorem Unit.ext (x y : Unit) : x = y := rfl

@[ext] protected theorem Thunk.ext : {a b : Thunk α} → a.get = b.get → a = b
  | {..}, {..}, heq => congrArg _ <| funext fun _ => heq
