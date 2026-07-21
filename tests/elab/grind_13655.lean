/-!
Regression test for issue #13655: the canonicalizer resynthesized an instance-implicit
`Nonempty α` proof occurring in a forall body skipped by `markNestedSubsingletons`,
producing a closed nested proof lacking the `Grind.nestedProof` wrapper. The resulting
enode was distinct from the correctly wrapped occurrences, and congruence closure failed
to detect the contradiction.
-/
set_option warn.sorry false
namespace Mwe

opaque P {α : Type} (a : α) : Prop

/--
`f` carries a `Nonempty α` instance-implicit argument.
The canonicalizer resynthesizes it if possible.
-/
opaque f {α : Type} [_n : Nonempty α] (a : α) : α := sorry

opaque aux {α : Type} (a : α) (_h : P a) : α := sorry

inductive Mem {α : Type} : α → List α → Prop where
  | head {a : α} {as : List α} : Mem a (a :: as)
  | tail {a b : α} {as : List α} : Mem a as → Mem a (b :: as)

@[simp] theorem mem_f_dep {α : Type} (a : α) (_h : P a) :
    haveI : Nonempty α := ⟨aux a _h⟩
    Mem (f a) [a] := sorry

grind_pattern mem_f_dep => Mem (@f α ⟨aux a _h⟩ a) [a]

@[simp] theorem mem_f_indep [n : Nonempty α] (a : α) (_h : P a) :
    Mem (f a) [a] := sorry

grind_pattern mem_f_indep => Mem (f a) [a]

end Mwe
open Mwe

/--
The `Nonempty α` proof in `mem_f_dep`'s body captures `_h`, so `markNestedSubsingletons`
skips the body. The canonicalizer must not resynthesize the unwrapped proof; the forall
stays dependent, and the instantiated body is preprocessed (and wrapped) by
`propagateForallPropUp`.
-/
example {α : Type} [Nonempty α] (x c : α)
    (hc : (f x) = c)
    (this : P x)
    (notMem : ¬ Mem c [x]) : False := by
  grind only [usr mem_f_dep]

/-- Same as above, but the `Nonempty α` instance cannot be resynthesized. -/
example {α : Type} (x c : α)
    (hc : (haveI : Nonempty α := sorry; f x) = c)
    (this : P x)
    (notMem : ¬ Mem c [x]) : False := by
  grind only [usr mem_f_dep]

/-- The `Nonempty α` proof in `mem_f_indep`'s body is closed, so it is wrapped eagerly. -/
example [Nonempty α] (x c : α)
    (hc : (f x) = c)
    (this : P x)
    (notMem : ¬ Mem c [x]) : False := by
  grind only [usr mem_f_indep]
