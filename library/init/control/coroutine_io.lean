/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.io init.control.coroutine

/-! A variant of `coroutine` on top of `io`. Implementation. -/

universes u v w r s

namespace coroutine_io
variables {α δ β γ : Type}

export coroutine_result_core (done yielded)

/-- `resume c a` resumes/invokes the coroutine_io `c` with input `a`. -/
@[inline] def resume : coroutine_io α δ β → α → io (coroutine_result_io α δ β)
| (mk k) a := k a

@[inline] protected def pure (b : β) : coroutine_io α δ β :=
mk $ λ _, pure (done b)

/-- Read the input argument passed to the coroutine.
    Remark: should we use a different name? I added an instance [monad_reader] later. -/
@[inline] protected def read : coroutine_io α δ α :=
mk $ λ a, pure (done a)

/-- Return the control to the invoker with result `d` -/
@[inline] protected def yield (d : δ) : coroutine_io α δ punit :=
mk $ λ a : α, pure $ yielded d (coroutine_io.pure ⟨⟩)

/-
TODO(Leo): following relations have been commented because Lean4 is currently
accepting non-terminating programs.

/-- Auxiliary relation for showing that bind/pipe terminate -/
inductive direct_subcoroutine_io : coroutine_io α δ β → coroutine_io α δ β → Prop
| mk : ∀ (k : α → coroutine_result α δ β) (a : α) (d : δ) (c : coroutine_io α δ β), k a = yielded d c → direct_subcoroutine_io c (mk k)

theorem direct_subcoroutine_wf : well_founded (@direct_subcoroutine_io α δ β) :=
begin
  constructor, intro c,
  apply @coroutine.ind _ _ _
          (λ c, acc direct_subcoroutine_io c)
          (λ r, ∀ (d : δ) (c : coroutine_io α δ β), r = yielded d c → acc direct_subcoroutine_io c),
  { intros k ih, dsimp at ih, constructor, intros c' h, cases h, apply ih h_a h_d, assumption },
  { intros, contradiction },
  { intros d c ih d₁ c₁ heq, injection heq, subst c, assumption }
end

/-- Transitive closure of direct_subcoroutine. It is not used here, but may be useful when defining
    more complex procedures. -/
def subcoroutine_io : coroutine_io α δ β → coroutine_io α δ β → Prop :=
tc direct_subcoroutine_io

theorem subcoroutine_wf : well_founded (@subcoroutine_io α δ β) :=
tc.wf direct_subcoroutine_wf

-- Local instances for proving termination by well founded relation

def bind_wf_inst : has_well_founded (Σ' a : coroutine_io α δ β, (β → coroutine_io α δ γ)) :=
{ r  := psigma.lex direct_subcoroutine_io (λ _, empty_relation),
  wf := psigma.lex_wf direct_subcoroutine_wf (λ _, empty_wf) }

def pipe_wf_inst : has_well_founded (Σ' a : coroutine_io α δ β, coroutine_io δ γ β) :=
{ r  := psigma.lex direct_subcoroutine_io (λ _, empty_relation),
  wf := psigma.lex_wf direct_subcoroutine_wf (λ _, empty_wf) }

local attribute [instance] wf_inst₁ wf_inst₂

open well_founded_tactics

-/

protected def bind : coroutine_io α δ β → (β → coroutine_io α δ γ) → coroutine_io α δ γ
| (mk k) f := mk $ λ a, k a >>= λ r,
    match r, rfl : ∀ (n : _), n = r → _ with
    | done b, _      := coroutine_io.resume (f b) a
    | yielded d c, h :=
      -- have direct_subcoroutine_io c (mk k), { apply direct_subcoroutine.mk k a d, rw h },
      pure $ yielded d (bind c f)
--  using_well_founded { dec_tac := unfold_wf_rel >> process_lex (tactic.assumption) }

def pipe : coroutine_io α δ β → coroutine_io δ γ β → coroutine_io α γ β
| (mk k₁) (mk k₂) := mk $ λ a, do
  r ← k₁ a,
  match r, rfl : ∀ (n : _), n = r → _ with
  | done b, h        := pure (done b)
  | yielded d k₁', h := do
    r ← k₂ d,
    pure $ match r with
    | done b        := done b
    | yielded r k₂' :=
      -- have direct_subcoroutine_io k₁' (mk k₁), { apply direct_subcoroutine.mk k₁ a d, rw h },
      yielded r (pipe k₁' k₂')
-- using_well_founded { dec_tac := unfold_wf_rel >> process_lex (tactic.assumption) }

instance : monad (coroutine_io α δ) :=
{ pure := @coroutine_io.pure _ _,
  bind := @coroutine_io.bind _ _ }

instance : monad_reader α (coroutine_io α δ) :=
{ read := @coroutine_io.read _ _ }

instance (α δ : Type) : coroutine.monad_coroutine α δ (coroutine_io α δ) :=
{ yield  := coroutine_io.yield }

instance : monad_io (coroutine_io α δ) :=
{ monad_lift := λ _ x, mk (λ _, done <$> x) }

end coroutine_io
