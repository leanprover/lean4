/-
Copyright (c) 2016 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/
prelude

import init.meta.interactive

namespace native

inductive result (E : Type) (R : Type) : Type
| err {} : E → result
| ok {} : R → result

def unwrap_or {E T : Type} : result E T → T → T
| (result.err _) default := default
| (result.ok t) _ := t

def result.and_then {E T U : Type} : result E T → (T → result E U) → result E U
| (result.err e) _ := result.err e
| (result.ok t) f := f t

instance result_monad (E : Type) : monad (result E) :=
{pure := @result.ok E, bind := @result.and_then E,
 id_map := by intros; cases x; dsimp [result.and_then]; apply rfl,
 pure_bind := by intros; apply rfl,
 bind_assoc := by intros; cases x; simp [result.and_then]}

inductive resultT (M : Type → Type) (E : Type) (A : Type) : Type
| run : M (result E A) → resultT

section resultT
  variable {M : Type → Type}

  def resultT.pure [monad : monad M] {E A : Type} (x : A) : resultT M E A :=
    resultT.run $ return (result.ok x)

  def resultT.and_then [monad : monad M] {E A B : Type} : resultT M E A → (A → resultT M E B) → resultT M E B
  | (resultT.run action) f := resultT.run (do
  res_a ← action,
  -- a little ugly with this match
  match res_a with
  | result.err e := return (result.err e)
  | result.ok a := let (resultT.run actionB) := f a in actionB
  end)

  instance resultT_monad [m : monad M] (E : Type) : monad (resultT M E) :=
  {pure := @resultT.pure M m E, bind := @resultT.and_then M m E,
   id_map := begin
     intros, cases x,
     dsimp [resultT.and_then],
     assert h : @resultT.and_then._match_1 _ m E α _ resultT.pure = pure,
     { apply funext, intro x,
       cases x; simp [resultT.and_then._match_1, resultT.pure, resultT.and_then._match_2] },
     { rw [h, @monad.bind_pure _ (result E α) _] },
   end,
   pure_bind := begin
     intros,
     dsimp [resultT.pure, resultT.and_then, return, pure, bind],
     rw [monad.pure_bind], dsimp [resultT.and_then._match_1],
     cases f x, dsimp [resultT.and_then._match_2], apply rfl,
   end,
   bind_assoc := begin
     intros,
     cases x, dsimp [resultT.and_then, bind],
     apply congr_arg, rw [monad.bind_assoc],
     apply congr_arg, apply funext, intro,
     cases x with e a; dsimp [resultT.and_then._match_1, pure],
     { rw [monad.pure_bind], apply rfl },
     { cases f a, apply rfl },
   end}
end resultT

end native
