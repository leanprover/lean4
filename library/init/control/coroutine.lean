/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.control.monad init.wf init.control.reader

universes u v w r s

inductive coroutine_result_core (coroutine : Type (max u v w)) (α : Type u) (δ : Type v) (β : Type w) : Type (max u v w)
| done     {} : β → coroutine_result_core
| yielded {}  : δ → coroutine → coroutine_result_core

/--
   Asymmetric coroutines `coroutine α δ β` takes inputs of type `α`, yields elements of type `δ`,
   and produces an element of type `β`.

   Asymmetric coroutines are so called because they involve two types of control transfer operations:
   one for resuming/invoking a coroutine and one for suspending it, the latter returning
   control to the coroutine invoker. An asymmetric coroutine can be regarded as subordinate
   to its caller, the relationship between them being similar to that between a called and
   a calling routine.
 -/
inductive coroutine (α : Type u) (δ : Type v) (β : Type w) : Type (max u v w)
| mk    {} : (α → coroutine_result_core coroutine α δ β) → coroutine

abbreviation coroutine_result (α : Type u) (δ : Type v) (β : Type w) : Type (max u v w) :=
coroutine_result_core (coroutine α δ β) α δ β

namespace coroutine
variables {α : Type u} {δ : Type v} {β γ : Type w}

export coroutine_result_core (done yielded)

/-- `resume c a` resumes/invokes the coroutine `c` with input `a`. -/
@[inline] def resume : coroutine α δ β → α → coroutine_result α δ β
| (mk k) a := k a

@[inline] protected def pure (b : β) : coroutine α δ β :=
mk $ λ _, done b

/-- Read the input argument passed to the coroutine.
    Remark: should we use a different name? I added an instance [monad_reader] later. -/
@[inline] protected def read : coroutine α δ α :=
mk $ λ a, done a

/-- Run nested coroutine with transformed input argument. Like `reader_t.adapt`, but
    cannot change the input type. -/
@[inline] protected def adapt (f : α → α) (c : coroutine α δ β) : coroutine α δ β :=
mk $ λ a, c.resume (f a)

/-- Return the control to the invoker with result `d` -/
@[inline] protected def yield (d : δ) : coroutine α δ punit :=
mk $ λ a : α, yielded d (coroutine.pure ⟨⟩)

/-
TODO(Leo): following relations have been commented because Lean4 is currently
accepting non-terminating programs.

/-- Auxiliary relation for showing that bind/pipe terminate -/
inductive direct_subcoroutine : coroutine α δ β → coroutine α δ β → Prop
| mk : ∀ (k : α → coroutine_result α δ β) (a : α) (d : δ) (c : coroutine α δ β), k a = yielded d c → direct_subcoroutine c (mk k)

theorem direct_subcoroutine_wf : well_founded (@direct_subcoroutine α δ β) :=
begin
  constructor, intro c,
  apply @coroutine.ind _ _ _
          (λ c, acc direct_subcoroutine c)
          (λ r, ∀ (d : δ) (c : coroutine α δ β), r = yielded d c → acc direct_subcoroutine c),
  { intros k ih, dsimp at ih, constructor, intros c' h, cases h, apply ih h_a h_d, assumption },
  { intros, contradiction },
  { intros d c ih d₁ c₁ heq, injection heq, subst c, assumption }
end

/-- Transitive closure of direct_subcoroutine. It is not used here, but may be useful when defining
    more complex procedures. -/
def subcoroutine : coroutine α δ β → coroutine α δ β → Prop :=
tc direct_subcoroutine

theorem subcoroutine_wf : well_founded (@subcoroutine α δ β) :=
tc.wf direct_subcoroutine_wf

-- Local instances for proving termination by well founded relation

def bind_wf_inst : has_well_founded (Σ' a : coroutine α δ β, (β → coroutine α δ γ)) :=
{ r  := psigma.lex direct_subcoroutine (λ _, empty_relation),
  wf := psigma.lex_wf direct_subcoroutine_wf (λ _, empty_wf) }

def pipe_wf_inst : has_well_founded (Σ' a : coroutine α δ β, coroutine δ γ β) :=
{ r  := psigma.lex direct_subcoroutine (λ _, empty_relation),
  wf := psigma.lex_wf direct_subcoroutine_wf (λ _, empty_wf) }

local attribute [instance] wf_inst₁ wf_inst₂

open well_founded_tactics

-/

protected def bind : coroutine α δ β → (β → coroutine α δ γ) → coroutine α δ γ
| (mk k) f := mk $ λ a,
    match k a, rfl : ∀ (n : _), n = k a → _ with
    | done b, _      := coroutine.resume (f b) a
    | yielded d c, h :=
      -- have direct_subcoroutine c (mk k), { apply direct_subcoroutine.mk k a d, rw h },
      yielded d (bind c f)
--  using_well_founded { dec_tac := unfold_wf_rel >> process_lex (tactic.assumption) }

def pipe : coroutine α δ β → coroutine δ γ β → coroutine α γ β
| (mk k₁) (mk k₂) := mk $ λ a,
  match k₁ a, rfl : ∀ (n : _), n = k₁ a → _ with
  | done b, h        := done b
  | yielded d k₁', h :=
    match k₂ d with
    | done b        := done b
    | yielded r k₂' :=
      -- have direct_subcoroutine k₁' (mk k₁), { apply direct_subcoroutine.mk k₁ a d, rw h },
      yielded r (pipe k₁' k₂')
-- using_well_founded { dec_tac := unfold_wf_rel >> process_lex (tactic.assumption) }

private def finish_aux (f : δ → α) : coroutine α δ β → α → list δ → list δ × β
| (mk k) a ds :=
  match k a with
  | done b       := (ds.reverse, b)
  | yielded d k' := finish_aux k' (f d) (d::ds)

/-- Run a coroutine to completion, feeding back yielded items after transforming them with `f`. -/
def finish (f : δ → α) : coroutine α δ β → α → list δ × β :=
λ k a, finish_aux f k a []

instance : monad (coroutine α δ) :=
{ pure := @coroutine.pure _ _,
  bind := @coroutine.bind _ _ }

instance : monad_reader α (coroutine α δ) :=
{ read := @coroutine.read _ _ }

end coroutine

/-- Auxiliary class for lifiting `yield` -/
class monad_coroutine (α : out_param (Type u)) (δ : out_param (Type v)) (m : Type w → Type r) :=
(yield {} : δ → m punit)

instance (α : Type u) (δ : Type v) : monad_coroutine α δ (coroutine α δ) :=
{ yield  := coroutine.yield }

instance monad_coroutine_trans (α : Type u) (δ : Type v) (m : Type w → Type r) (n : Type w → Type s)
                               [has_monad_lift m n] [monad_coroutine α δ m] : monad_coroutine α δ n :=
{ yield := λ d, monad_lift (monad_coroutine.yield d : m _) }

export monad_coroutine (yield)
