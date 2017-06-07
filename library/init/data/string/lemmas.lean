/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.meta

namespace string
lemma empty_ne_str (c : char) (s : string) : empty ≠ str s c :=
begin cases s, unfold str empty, intro h, injection h, contradiction end

lemma str_ne_empty (c : char) (s : string) : str s c ≠ empty :=
begin cases s, unfold str empty, intro h, injection h, contradiction end

lemma str_ne_str_left {c₁ c₂ : char} (s₁ s₂ : string) : c₁ ≠ c₂ → str s₁ c₁ ≠ str s₂ c₂ :=
begin cases s₁, cases s₂, intros h₁ h₂, unfold str at h₂, injection h₂, injection h, contradiction end

lemma str_ne_str_right (c₁ c₂ : char) {s₁ s₂ : string} : s₁ ≠ s₂ → str s₁ c₁ ≠ str s₂ c₂ :=
begin cases s₁, cases s₂, intros h₁ h₂, unfold str at h₂, injection h₂, injection h, subst data, contradiction end
end string
