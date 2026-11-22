import Std.WP
import Std.Do

/-!
The triple notation `⦃ P ⦄ x ⦃ Q ⦄` is scoped. Outside `open Std.WP` it reports how to make it
available, while strict-implicit binders and the scoped notations keep their meaning.
-/

/--
error: to use the triple notation `⦃ P ⦄ x ⦃ Q ⦄`, please include `import Std.WP` and `open Std.WP`
-/
#guard_msgs in
example : ⦃ True ⦄ (pure () : Id Unit) ⦃ fun _ => True ⦄ := sorry

/--
error: to use the triple notation `⦃ P ⦄ x ⦃ Q ⦄`, please include `import Std.WP` and `open Std.WP`
-/
#guard_msgs in
example : ⦃ True ⦄ (pure () : Id Unit) ⦃ fun _ => True; True ⦄ := sorry

example : ∀ ⦃n : Nat⦄, n = n := fun _ => rfl

example : ⦃n : Nat⦄ → n = n := fun _ => rfl

section
open Std.WP

example : (⦃ True ⦄ (pure () : Id Unit) ⦃ fun _ => True ⦄) =
    Triple (pure () : Id Unit) True (fun _ => True) Lean.Order.bot := rfl

end

section
open Std.Do

example : (⦃⌜True⌝⦄ (pure () : Id Unit) ⦃⇓ _ => ⌜True⌝⦄) =
    Std.Do.Triple (pure () : Id Unit) ⌜True⌝ (⇓ _ => ⌜True⌝) := rfl

end
