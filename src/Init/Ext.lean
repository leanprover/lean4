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

* When `@[ext]` is applied to a structure, it generates `.ext` and `.ext_iff` theorems and registers
  them for the `ext` tactic.

* When `@[ext]` is applied to a theorem, the theorem is registered for the `ext` tactic, and it generates an `ext_iff` theorem.
  The name of the theorem is from adding the suffix `_iff` to the theorem name.

* An optional natural number argument, e.g. `@[ext 9000]`, specifies a priority for the lemma. Higher-priority lemmas are chosen first, and the default is `1000`.

* The flag `@[ext (iff := false)]` prevents it from generating an `ext_iff` theorem.

* The flag `@[ext (flat := false)]` causes generated structure extensionality theorems to show inherited fields based on their representation,
  rather than flattening the parents' fields into the lemma's equality hypotheses.
  structures in the generated extensionality theorems.
-/
syntax (name := ext) "ext" (ppSpace extIff)? (ppSpace extFlat)? (ppSpace prio)? : attr
end Parser.Attr

-- TODO: rename this namespace?
-- Remark: `ext` has scoped syntax, Mathlib may depend on the actual namespace name.
namespace Elab.Tactic.Ext
/--
Creates the type of the extensionality theorem for the given structure,
elaborating to `x.1 = y.1 → x.2 = y.2 → x = y`, for example.
-/
scoped syntax (name := extType) "ext_type% " (Parser.Attr.extFlat)? ppSpace ident : term

/--
`declare_ext_theorems_for A` declares the extensionality theorems for the structure `A`.

These theorems state that two expressions with the structure type are equal if their fields are equal.
-/
syntax (name := declareExtTheoremFor) "declare_ext_theorems_for " (Parser.Attr.extIff ppSpace)? (Parser.Attr.extFlat ppSpace)? ident (ppSpace prio)? : command

macro_rules | `(declare_ext_theorems_for $[(iff := false%$iff?)]? $[(flat := false%$flat?)]? $struct:ident $[$prio?]?) => do
  let names ← Macro.resolveGlobalName struct.getId.eraseMacroScopes
  let name ← match names.filter (·.2.isEmpty) with
    | [] => Macro.throwError s!"unknown constant {struct.getId}"
    | [(name, _)] => pure name
    | _ => Macro.throwError s!"ambiguous name {struct.getId}"
  let extName := mkIdentFrom struct (canonical := true) <| name.mkStr "ext"
  `(@[ext $[(iff := false%$iff?)]? $[$prio?:prio]?] protected theorem $extName:ident : ext_type% $[(flat := false%$flat?)]? $struct:ident :=
      fun {..} {..} => by intros; subst_eqs; rfl)

/--
Creates the type of the iff variant of the given user extensionality theorem,
elaborating to `x = y ↔ x.1 = y.1 ∧ x.2 = y.2`, for example.
-/
scoped syntax (name := deriveExtIffType) "derive_ext_iff_type% " ident : term

/--
`derive_ext_if_theorem ext_thm` declares the iff variant of the extensionality theorem `ext_thm`.
-/
syntax (name := deriveExtIffTheoremFor) "derive_ext_iff_theorem " ident : command

macro_rules | `(derive_ext_iff_theorem $extThm:ident) => do
  let names ← Macro.resolveGlobalName extThm.getId.eraseMacroScopes
  let name ← match names.filter (·.2.isEmpty) with
    | [] => Macro.throwError s!"unknown constant {extThm.getId}"
    | [(name, _)] => pure name
    | _ => Macro.throwError s!"ambiguous name {extThm.getId}"
  let extIffThm := mkIdentFrom extThm (canonical := true) <|
    match name with
    | .str name' n => .str name' (n ++ "_iff")
    | _ => .str name "ext_iff"
  let body : Term ← `(by
    intros
    refine ⟨?_, ?_⟩
    · intro h; cases h; and_intros <;> (intros; first | rfl | simp | fail "Failed to prove converse of ext theorem")
    · intro; (repeat cases ‹_ ∧ _›); apply $extThm <;> assumption)
  if name.getRoot == name then
    -- In root namespace, cannot protect.
    `(theorem $extIffThm:ident : derive_ext_iff_type% $extThm:ident := $body)
  else
    `(protected theorem $extIffThm:ident : derive_ext_iff_type% $extThm:ident := $body)

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

attribute [ext] funext propext Subtype.eq

@[ext] theorem Prod.ext : {x y : Prod α β} → x.fst = y.fst → x.snd = y.snd → x = y
  | ⟨_,_⟩, ⟨_,_⟩, rfl, rfl => rfl

@[ext] theorem PProd.ext : {x y : PProd α β} → x.fst = y.fst → x.snd = y.snd → x = y
  | ⟨_,_⟩, ⟨_,_⟩, rfl, rfl => rfl

@[ext] theorem Sigma.ext : {x y : Sigma β} → x.fst = y.fst → HEq x.snd y.snd → x = y
  | ⟨_,_⟩, ⟨_,_⟩, rfl, .rfl => rfl

@[ext] theorem PSigma.ext : {x y : PSigma β} → x.fst = y.fst → HEq x.snd y.snd → x = y
  | ⟨_,_⟩, ⟨_,_⟩, rfl, .rfl => rfl

@[ext] protected theorem PUnit.ext (x y : PUnit) : x = y := rfl
protected theorem Unit.ext (x y : Unit) : x = y := rfl
