import Std.WP
import Std.Tactic.Do

/-!
A monad may register a bespoke `WP` instance next to its `WPMonad` instance. The goal then
carries the registered instance while a spec instantiated from `[WPMonad m …]` carries the
blanket `WPMonad.toWP` route. Rule construction canonicalizes both spellings to the instance
that `synthInstance` returns, so `Spec.bind` applies either way. `Identity` states the `toWP`
field by name, `Identity2` via `inferInstance`.
-/

set_option experimental.vcgen true
open Std.WP Lean.Order

universe u
variable {α : Type u}

structure Identity (α : Type u) where
  run : α

instance : Monad Identity where
  pure x := ⟨x⟩
  bind x f := f x.run

instance : LawfulMonad Identity :=
  LawfulMonad.mk' Identity
    (id_map := fun _ => rfl)
    (pure_bind := fun _ _ => rfl)
    (bind_assoc := fun _ _ _ => rfl)

instance Identity.instWP : WP (Identity α) α Prop EStack⟨⟩ where
  wpTrans x := ⟨fun post _ => post x.run⟩
  wp_trans_monotone x := fun _ _ _ _ _ hpost => hpost x.run

instance Identity.instWPMonad : WPMonad Identity Prop EStack⟨⟩ where
  toWP _ := Identity.instWP
  pure_le_wp_pure x post epost := PartialOrder.rel_refl
  bind_le_wp_bind x f post epost := PartialOrder.rel_refl

theorem Identity.of_run_eq_wp {x : α} {prog : Identity α}
    (h : Identity.run prog = x) (P : α → Prop)
    (hwp : wp prog P ()) : P x := by
  simp_all [wp, WP.wpTrans, ← h]

def rev (xs : List α) : Identity (List α) := do
  let mut out := []
  for x in xs do
    out := x :: out
  return out

example {xs : List α} : (rev xs).run = xs.reverse := by
  generalize h : (rev xs).run = x
  apply Identity.of_run_eq_wp h
  simp only [rev]
  vcgen invariants
  · fun pref _suff out => out = pref.reverse
  with finish

structure Identity2 (α : Type u) where
  run : α

instance : Monad Identity2 where
  pure x := ⟨x⟩
  bind x f := f x.run

instance : LawfulMonad Identity2 :=
  LawfulMonad.mk' Identity2
    (id_map := fun _ => rfl)
    (pure_bind := fun _ _ => rfl)
    (bind_assoc := fun _ _ _ => rfl)

instance Identity2.instWP : WP (Identity2 α) α Prop EStack⟨⟩ where
  wpTrans x := ⟨fun post _ => post x.run⟩
  wp_trans_monotone x := fun _ _ _ _ _ hpost => hpost x.run

instance Identity2.instWPMonad : WPMonad Identity2 Prop EStack⟨⟩ where
  toWP _ := inferInstance
  pure_le_wp_pure x post epost := PartialOrder.rel_refl
  bind_le_wp_bind x f post epost := PartialOrder.rel_refl

theorem Identity2.of_run_eq_wp {x : α} {prog : Identity2 α}
    (h : Identity2.run prog = x) (P : α → Prop)
    (hwp : wp prog P ()) : P x := by
  simp_all [wp, WP.wpTrans, ← h]

def rev2 (xs : List α) : Identity2 (List α) := do
  let mut out := []
  for x in xs do
    out := x :: out
  return out

example {xs : List α} : (rev2 xs).run = xs.reverse := by
  generalize h : (rev2 xs).run = x
  apply Identity2.of_run_eq_wp h
  simp only [rev2]
  vcgen invariants
  · fun pref _suff out => out = pref.reverse
  with finish
