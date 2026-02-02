import Std.Do
open Std.Do

-- This failed cryptically for `α : Type u` because the `post` macro expanded to `()` instead of `PUnit.unit`
axiom Option.of_wp_eq {α : Type u} {x : Option α} {prog : Option α} (h : prog = x) (P : Option α → Prop) :
    (⊢ₛ wp⟦prog⟧ post⟨fun a => ⌜P (some a)⌝, fun _ => ⌜P none⌝⟩) → P x
