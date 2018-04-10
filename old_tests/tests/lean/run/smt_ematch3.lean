namespace Ex
open nat
notation `⟦`:max a `⟧`:0 := cast (by simp) a

inductive vector (α : Type) : nat → Type
| nil {} : vector 0
| cons   : Π {n}, α → vector n → vector (succ n)

namespace vector
local attribute [simp] add_succ succ_add add_comm

variable {α : Type}

def app : Π {n m : nat}, vector α n → vector α m → vector α (n + m)
| 0        m nil        w := ⟦ w ⟧
| (succ n) m (cons a v) w := ⟦ cons a (app v w) ⟧

lemma app_nil_right {n : nat} (v : vector α n) : app v nil == v :=
begin induction v, reflexivity, {[smt] ematch_using [app, add_comm, zero_add, add_zero] }, end

def smt_cfg : smt_config :=
{ cc_cfg := {ac := ff}}

lemma app_assoc {n₁ n₂ n₃ : nat} (v₁ : vector α n₁) (v₂ : vector α n₂) (v₃ : vector α n₃) :
                     app v₁ (app v₂ v₃) == app (app v₁ v₂) v₃ :=
begin
  intros,
  induction v₁,
  {[smt] ematch_using [app, zero_add] },
  {[smt] with smt_cfg, iterate { ematch_using [app, add_succ, succ_add, add_comm, add_assoc] }}
end

def rev : Π {n : nat}, vector α n → vector α n
| 0     nil         := nil
| (n+1) (cons x xs) := app (rev xs) (cons x nil)

lemma rev_app : ∀ {n₁ n₂ : nat} (v₁ : vector α n₁) (v₂ : vector α n₂),
  rev (app v₁ v₂) == app (rev v₂) (rev v₁) :=
begin
  intros,
  induction v₁,
  {[smt] iterate {ematch_using [app, rev, zero_add, add_zero, add_comm, app_nil_right]}},
  {[smt] iterate {ematch_using [app, rev, zero_add, add_zero, add_comm, app_assoc, add_one]} }
end

end vector
end Ex
