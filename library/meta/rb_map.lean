/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import meta.cmp_result meta.name meta.format

meta_constant rb_map.{l₁ l₂} : Type.{l₁} → Type.{l₂} → Type.{max l₁ l₂ 1}

namespace rb_map
meta_constant mk_core {key : Type} (data : Type)        : (key → key → cmp_result) → rb_map key data
meta_constant size {key : Type} {data : Type}           : rb_map key data → nat
meta_constant insert {key : Type} {data : Type}         : rb_map key data → key → data → rb_map key data
meta_constant erase  {key : Type} {data : Type}         : rb_map key data → key → rb_map key data
meta_constant contains {key : Type} {data : Type}       : rb_map key data → key → bool
meta_constant find {key : Type} {data : Type}           : rb_map key data → key → option data
meta_constant min {key : Type} {data : Type}            : rb_map key data → option data
meta_constant max {key : Type} {data : Type}            : rb_map key data → option data
meta_constant fold {key : Type} {data : Type} {A :Type} : rb_map key data → A → (key → data → A → A) → A

inline meta_definition mk (key : Type) [has_cmp key] (data : Type) : rb_map key data :=
mk_core data has_cmp.cmp

open list
meta_definition of_list {key : Type} {data : Type} [has_cmp key] : list (key × data) → rb_map key data
| []           := mk key data
| ((k, v)::ls) := insert (of_list ls) k v

end rb_map

meta_definition nat_map [reducible] (data : Type) := rb_map nat data
namespace nat_map
  export rb_map (hiding mk)

  inline meta_definition mk (data : Type) : nat_map data :=
  rb_map.mk nat data
end nat_map

meta_definition name_map [reducible] (data : Type) := rb_map name data
namespace name_map
  export rb_map (hiding mk)

  inline meta_definition mk (data : Type) : name_map data :=
  rb_map.mk name data
end name_map

open rb_map bool prod
section
open format
variables {key : Type} {data : Type} [has_to_format key] [has_to_format data]
private meta_definition format_key_data (k : key) (d : data) (first : bool) : format :=
(cond first (to_fmt "") (to_fmt "," + line)) + to_fmt k + space + "←" + space + to_fmt d

meta_definition rb_map_has_to_format [instance] : has_to_format (rb_map key data) :=
has_to_format.mk (λ m,
  group ("⟨" + nest 1 (pr₁ (fold m (to_fmt "", tt) (λ k d p, (pr₁ p + format_key_data k d (pr₂ p), ff)))) + "⟩"))
end

section
variables {key : Type} {data : Type} [has_to_string key] [has_to_string data]
private meta_definition key_data_to_string (k : key) (d : data) (first : bool) : string :=
(cond first "" ", ") + to_string k + " ← " + to_string d

meta_definition rb_map_has_to_string [instance] : has_to_string (rb_map key data) :=
has_to_string.mk (λ m,
  "⟨" + (pr₁ (fold m ("", tt) (λ k d p, (pr₁ p + key_data_to_string k d (pr₂ p), ff)))) + "⟩")
end
