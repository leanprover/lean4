/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
prelude
import Init.Util

@[never_extract]
private def outOfBounds [Inhabited α] : α :=
  panic! "index out of bounds"

/--
The class `GetElem cont idx elem dom` implements the `xs[i]` notation.
When you write this, given `xs : cont` and `i : idx`, Lean looks for an instance
of `GetElem cont idx elem dom`. Here `elem` is the type of `xs[i]`, while
`dom` is whatever proof side conditions are required to make this applicable.
For example, the instance for arrays looks like
`GetElem (Array α) Nat α (fun xs i => i < xs.size)`.

The proof side-condition `dom xs i` is automatically dispatched by the
`get_elem_tactic` tactic, which can be extended by adding more clauses to
`get_elem_tactic_trivial`.
-/
class GetElem (cont : Type u) (idx : Type v) (elem : outParam (Type w)) (dom : outParam (cont → idx → Prop)) where
  /--
  The syntax `arr[i]` gets the `i`'th element of the collection `arr`.
  If there are proof side conditions to the application, they will be automatically
  inferred by the `get_elem_tactic` tactic.

  The actual behavior of this class is type-dependent,
  but here are some important implementations:
  * `arr[i] : α` where `arr : Array α` and `i : Nat` or `i : USize`:
    does array indexing with no bounds check and a proof side goal `i < arr.size`.
  * `l[i] : α` where `l : List α` and `i : Nat`: index into a list,
    with proof side goal `i < l.length`.
  * `stx[i] : Syntax` where `stx : Syntax` and `i : Nat`: get a syntax argument,
    no side goal (returns `.missing` out of range)

  There are other variations on this syntax:
  * `arr[i]`: proves the proof side goal by `get_elem_tactic`
  * `arr[i]!`: panics if the side goal is false
  * `arr[i]?`: returns `none` if the side goal is false
  * `arr[i]'h`: uses `h` to prove the side goal
  -/
  getElem (xs : cont) (i : idx) (h : dom xs i) : elem

  getElem? (xs : cont) (i : idx) [Decidable (dom xs i)] : Option elem :=
    if h : _ then some (getElem xs i h) else none

  getElem! [Inhabited elem] (xs : cont) (i : idx) [Decidable (dom xs i)] : elem :=
    match getElem? xs i h with | some e => e | none => outOfBounds

export GetElem (getElem getElem! getElem?)

/--
Searches environment for definitions or theorems that can be substituted in
for `exact?% to solve the goal.
 -/
syntax (name := Lean.Parser.Syntax.exact?) "exact?%" : term

@[inherit_doc getElem]
syntax:max term noWs "[" withoutPosition(term) "]" : term
macro_rules | `($x[$i]) => `(getElem $x $i (by get_elem_tactic))

@[inherit_doc getElem]
syntax term noWs "[" withoutPosition(term) "]'" term:max : term
macro_rules | `($x[$i]'$h) => `(getElem $x $i $h)

macro:max x:term noWs "[" i:term "]" noWs "?" : term => `(getElem? $x $i)
macro:max x:term noWs "[" i:term "]" noWs "!" : term => `(getElem! $x $i)

namespace Fin

instance [GetElem cont Nat elem dom] : GetElem cont (Fin n) elem fun xs i => dom xs i where
  getElem xs i h := getElem xs i.1 h

macro_rules
  | `(tactic| get_elem_tactic_trivial) => `(tactic| apply Fin.val_lt_of_le; get_elem_tactic_trivial; done)

end Fin

namespace List

instance : GetElem (List α) Nat α fun as i => i < as.length where
  getElem as i h := as.get ⟨i, h⟩

@[simp] theorem cons_getElem_zero (a : α) (as : List α) (h : 0 < (a :: as).length) : getElem (a :: as) 0 h = a := by
  rfl

@[simp] theorem cons_getElem_succ (a : α) (as : List α) (i : Nat) (h : i + 1 < (a :: as).length) : getElem (a :: as) (i+1) h = getElem as i (Nat.lt_of_succ_lt_succ h) := by
  rfl

theorem get_drop_eq_drop (as : List α) (i : Nat) (h : i < as.length) : as[i] :: as.drop (i+1) = as.drop i :=
  match as, i with
  | _::_, 0   => rfl
  | _::_, i+1 => get_drop_eq_drop _ i _

end List

namespace Array

instance : GetElem (Array α) Nat α fun xs i => LT.lt i xs.size where
  getElem xs i h := xs.get ⟨i, h⟩

end Array

namespace Lean.Syntax

instance : GetElem Syntax Nat Syntax fun _ _ => True where
  getElem stx i _ := stx.getArg i

end Lean.Syntax
