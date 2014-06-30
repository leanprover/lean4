-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import logic

-- Function extensionality
axiom funext : ∀ {A : Type} {B : A → Type} {f g : Π x, B x} (H : ∀ x, f x = g x), f = g
