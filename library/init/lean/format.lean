/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.control.except init.control.reader init.control.state
universes u v

namespace lean

inductive format
| nil          : format
| line         : format
| text         : string → format
| nest         : nat → format → format
| compose      : bool → format → format → format
| choice       : format → format → format

namespace format
instance : has_append format     := ⟨compose ff⟩
instance : has_coe string format := ⟨text⟩

def join (xs : list format) : format :=
xs.foldl (++) ""

def flatten : format → format
| nil                  := nil
| line                 := text " "
| f@(text _)           := f
| (nest _ f)           := flatten f
| (choice f _)         := flatten f
| f@(compose tt _ _)   := f
| f@(compose ff f₁ f₂) := compose tt (flatten f₁) (flatten f₂)

def group : format → format
| nil                := nil
| f@(text _)         := f
| f@(compose tt _ _) := f
| f                  := choice (flatten f) f

structure space_result :=
(found    := ff)
(exceeded := ff)
(space    := 0)

/-
TODO: mark as `@[inline]` as soon as we fix the code inliner.
-/
private def merge (w : nat) (r₁ : space_result) (r₂ : thunk space_result) : space_result :=
if r₁.exceeded || r₁.found then r₁
else let y := r₂ () in
     if y.exceeded || y.found then y
     else let new_space := r₁.space + y.space in
          { space := new_space, exceeded := new_space > w }

def space_upto_line : format → nat → space_result
| nil               w := {}
| line              w := { found := tt }
| (text s)          w := { space := s.length, exceeded := s.length > w }
| (compose _ f₁ f₂) w := merge w (space_upto_line f₁ w) (space_upto_line f₂ w)
| (nest _ f)        w := space_upto_line f w
| (choice f₁ f₂)    w := space_upto_line f₂ w

def space_upto_line' : list (nat × format) → nat → space_result
| []      w := {}
| (p::ps) w := merge w (space_upto_line p.2 w) (space_upto_line' ps w)

def be : nat → nat → string → list (nat × format) → string
| w k out []                           := out
| w k out ((i, nil)::z)                := be w k out z
| w k out ((i, (compose _ f₁ f₂))::z)  := be w k out ((i, f₁)::(i, f₂)::z)
| w k out ((i, (nest n f))::z)         := be w k out ((i+n, f)::z)
| w k out ((i, text s)::z)             := be w (k + s.length) (out ++ s) z
| w k out ((i, line)::z)               := be w i ((out ++ "\n").pushn ' ' i) z
| w k out ((i, choice f₁ f₂)::z)       :=
  let r := merge w (space_upto_line f₁ w) (space_upto_line' z w) in
  if r.exceeded then be w k out ((i, f₂)::z) else be w k out ((i, f₁)::z)

def pretty (f : format) (w : nat := 80) : string :=
be w 0 "" [(0, f)]

@[inline] def bracket (l : string) (f : format) (r : string) : format :=
group (nest l.length $ l ++ f ++ r)

@[inline] def paren (f : format) : format :=
bracket "(" f ")"

@[inline] def sbracket (f : format) : format :=
bracket "[" f "]"

end format

open lean.format

class has_to_format (α : Type u) :=
(to_format : α → format)

export lean.has_to_format (to_format)

instance to_string_to_format {α : Type u} [has_to_string α] : has_to_format α :=
⟨text ∘ to_string⟩

instance string_has_to_format : has_to_format string := ⟨format.text⟩

def list.to_format {α : Type u} [has_to_format α] : list α → format
| [] := "[]"
| xs := sbracket $ join $ list.intersperse ("," ++ line) $ xs.map to_format

instance list_has_to_format {α : Type u} [has_to_format α] : has_to_format (list α) :=
⟨list.to_format⟩

instance {α : Type u} {β : Type v} [has_to_format α] [has_to_format β] : has_to_format (prod α β) :=
⟨λ ⟨a, b⟩, paren $ to_format a ++ "," ++ line ++ to_format b⟩

end lean
