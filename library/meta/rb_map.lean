/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import meta.cmp_result meta.name

meta_constant rb_map.{l₁ l₂} : Type.{l₁} → Type.{l₂} → Type.{max l₁ l₂ 1}

namespace rb_map
meta_constant mk {key : Type} (data : Type)             : (key → key → cmp_result) → rb_map key data
meta_constant size {key : Type} {data : Type}           : rb_map key data → nat
meta_constant insert {key : Type} {data : Type}         : rb_map key data → key → data → rb_map key data
meta_constant erase  {key : Type} {data : Type}         : rb_map key data → key → rb_map key data
meta_constant contains {key : Type} {data : Type}       : rb_map key data → key → bool
meta_constant find {key : Type} {data : Type}           : rb_map key data → key → option data
meta_constant min {key : Type} {data : Type}            : rb_map key data → option data
meta_constant max {key : Type} {data : Type}            : rb_map key data → option data
meta_constant fold {key : Type} {data : Type} {A :Type} : rb_map key data → A → (key → data → A → A) → A

open list
meta_definition of_list {key : Type} {data : Type} (cmp : key → key → cmp_result) : list (key × data) → rb_map key data
| []           := mk data cmp
| ((k, v)::ls) := insert (of_list cmp ls) k v

end rb_map

meta_definition nat_map (data : Type) := rb_map nat data
namespace nat_map
  export rb_map (hiding mk)

  meta_definition mk (data : Type) : nat_map data :=
  rb_map.mk data nat.cmp
end nat_map

meta_definition name_map (data : Type) := rb_map name data
namespace name_map
  export rb_map (hiding mk)

  meta_definition mk (data : Type) : name_map data :=
  rb_map.mk data name.cmp
end name_map
