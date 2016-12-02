/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.meta

namespace string
lemma empty_ne_str (c : char) (s : string) : empty ≠ str c s :=
begin intro h, contradiction end

lemma str_ne_empty (c : char) (s : string) : str c s ≠ empty :=
begin intro h, contradiction end

lemma str_ne_str_left {c₁ c₂ : char} (s₁ s₂ : string) : c₁ ≠ c₂ → str c₁ s₁ ≠ str c₂ s₂ :=
begin intros h₁ h₂, unfold str at h₂, injection h₂, contradiction end

lemma str_ne_str_right (c₁ c₂ : char) {s₁ s₂ : string} : s₁ ≠ s₂ → str c₁ s₁ ≠ str c₂ s₂ :=
begin intros h₁ h₂, unfold str at h₂, injection h₂, contradiction end
end string
