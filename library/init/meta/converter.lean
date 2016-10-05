/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Converter monad for building simplifiers.
-/
prelude
import init.meta.tactic init.meta.simp_tactic init.meta.defeq_simp_tactic
open tactic

meta structure conv_result (A : Type) :=
(val : A) (rhs : expr) (proof : option expr)

meta def conv (A : Type) : Type :=
name → expr → tactic (conv_result A)

namespace conv

meta def lhs : conv expr :=
λ r e, return ⟨e, e, none⟩

meta def change (new_p : pexpr) : conv unit :=
λ r e, do
  new_e ← to_expr new_p,
  unify e new_e,
  return ⟨(), new_e, none⟩

protected meta def pure {A : Type} : A → conv A :=
λ a r e, return ⟨a, e, none⟩

private meta def join_proofs (r : name) (o₁ o₂ : option expr) : tactic (option expr) :=
match o₁, o₂ with
| none,    _       := return o₂
| _,       none    := return o₁
| some p₁, some p₂ := do
  env ← get_env,
  match (environment.trans_for env r) with
  | (some trans) := do pr ← mk_app trans [p₁, p₂], return $ some pr
  | none         := fail $ "converter failed, relation '" ++ r^.to_string ++ "' is not transitive"
  end
end

protected meta def seq {A B : Type} (c₁ : conv (A → B)) (c₂ : conv A) : conv B :=
λ r e, do
  ⟨fn, e₁, pr₁⟩ ← c₁ r e,
  ⟨a,  e₂, pr₂⟩ ← c₂ r e₁,
  pr            ← join_proofs r pr₁ pr₂,
  return ⟨fn a, e₂, pr⟩

protected meta def fail {A : Type} : conv A :=
λ r e, failed

protected meta def orelse {A : Type} (c₁ : conv A) (c₂ : conv A) : conv A :=
λ r e, c₁ r e <|> c₂ r e

protected meta def map {A B : Type} (f : A → B) (c : conv A) : conv B :=
λ r e, do
  ⟨a, e₁, pr⟩ ← c r e,
  return ⟨f a, e₁, pr⟩

protected meta def bind {A B : Type} (c₁ : conv A) (c₂ : A → conv B) : conv B :=
λ r e, do
  ⟨a, e₁, pr₁⟩ ← c₁ r e,
  ⟨b, e₂, pr₂⟩ ← c₂ a r e₁,
  pr           ← join_proofs r pr₁ pr₂,
  return ⟨b, e₂, pr⟩

meta instance : monad conv :=
{ map  := @conv.map,
  ret  := @conv.pure,
  bind := @conv.bind }

meta instance : alternative conv :=
{ map     := @conv.map,
  pure    := @conv.pure,
  seq     := @conv.seq,
  failure := @conv.fail,
  orelse  := @conv.orelse }

meta def whnf_core (m : transparency) : conv unit :=
λ r e, do n ← whnf_core m e, return ⟨(), n, none⟩

meta def whnf : conv unit :=
conv.whnf_core reducible

meta def dsimp : conv unit :=
λ r e, do n ← defeq_simp e, return ⟨(), n, none⟩

meta def try (c : conv unit) : conv unit :=
c <|> return ()

meta def trace {A : Type} [has_to_tactic_format A] (a : A) : conv unit :=
λ r e, tactic.trace a >> return ⟨(), e, none⟩

meta def trace_lhs : conv unit :=
lhs >>= trace

meta def apply_lemmas_core (s : simp_lemmas) (prove : tactic unit) : conv unit :=
λ r e, do
  (new_e, pr) ← simp_lemmas_apply s prove r e,
  return ⟨(), new_e, some pr⟩

meta def apply_lemmas (s : simp_lemmas) : conv unit :=
apply_lemmas_core s failed

private meta def mk_refl_proof (r : name) (e : expr) : tactic expr :=
do env ← get_env,
   match (environment.refl_for env r) with
   | (some refl) := do pr ← mk_app refl [e], return pr
   | none        := fail $ "converter failed, relation '" ++ r^.to_string ++ "' is not reflexive"
   end

meta def to_tactic (c : conv unit) : name → expr → tactic (expr × expr) :=
λ r e, do
  ⟨u, e₁, o⟩ ← c r e,
  match o with
  | none   := do p ← mk_refl_proof r e, return (e₁, p)
  | some p := return (e₁, p)
  end

meta def lift_tactic {A : Type} (t : tactic A) : conv A :=
λ r e, do a ← t, return ⟨a, e, none⟩

meta def apply_simp_set (attr_name : name) : conv unit :=
lift_tactic (get_user_simp_lemmas attr_name) >>= apply_lemmas

/- TODO(Leo): add more primitives and combinators. Example: congruence, funext, etc -/

end conv
