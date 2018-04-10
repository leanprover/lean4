universe variables u
namespace foo
variables {α : Type u}

open smt_tactic
meta def no_ac : smt_config :=
{ cc_cfg := { ac := ff }}

meta def blast : tactic unit :=
using_smt_with no_ac $ intros >> iterate (ematch >> try close)

section add_comm_monoid
variables [add_comm_monoid α]
attribute [ematch] add_comm add_assoc

theorem add_comm_three  (a b c : α) : a + b + c = c + b + a :=
by blast

theorem add.comm4 : ∀ (n m k l : α), n + m + (k + l) = n + k + (m + l) :=
by blast
end add_comm_monoid


section group
variable [group α]
attribute [ematch] mul_assoc mul_left_inv one_mul

theorem inv_mul_cancel_left (a b : α) : a⁻¹ * (a * b) = b :=
by blast
end group


namespace subt
constant subt : nat → nat → Prop
axiom subt_trans {a b c : nat} : subt a b → subt b c → subt a c
attribute [ematch] subt_trans

lemma ex (a b c d : nat) : subt a b → subt b c → subt c d → subt a d :=
by blast
end subt


section ring
variables [ring α] (a b : α)
attribute [ematch] zero_mul
lemma ex2 : a = 0 → a * b = 0 :=
by blast

definition ex1 (a b : int) : a = 0 → a * b = 0 :=
by blast
end ring


namespace cast1
constant C : nat → Type
constant f : ∀ n, C n → C n
axiom fax (n : nat) (a : C (2*n)) : (: f (2*n) a :) = a
attribute [ematch] fax

lemma ex3 (n m : nat) (a : C n) : n = 2*m → f n a = a :=
by blast
end cast1


namespace cast2
constant C : nat → Type
constant f : ∀ n, C n → C n
constant g : ∀ n, C n → C n → C n
axiom gffax (n : nat) (a b : C n) : (: g n (f n a) (f n b) :) = a
attribute [ematch] gffax

lemma ex4 (n m : nat) (a c : C n) (b : C m) : n = m → a == f m b → g n a (f n c) == b :=
by blast
end cast2


namespace cast3
constant C : nat → Type
constant f : ∀ n, C n → C n
constant g : ∀ n, C n → C n → C n
axiom gffax (n : nat) (a b : C n) : (: g n a b :) = a
attribute [ematch] gffax

lemma ex5 (n m : nat) (a c : C n) (b : C m) (e : m = n) : a == b → g n a a == b :=
by blast
end cast3

namespace tuple
constant {α} tuple: Type α → nat → Type α
constant nil {α : Type u} : tuple α 0
constant append {α : Type u} {n m : nat} : tuple α n → tuple α m → tuple α (n + m)
infix ` ++ ` := append
axiom append_assoc {α : Type u} {n₁ n₂ n₃ : nat} (v₁ : tuple α n₁) (v₂ : tuple α n₂) (v₃ : tuple α n₃) :
  (v₁ ++ v₂) ++ v₃ == v₁ ++ (v₂ ++ v₃)
attribute [ematch] append_assoc

variables {p m n q : nat}
variables {xs : tuple α m}
variables {ys : tuple α n}
variables {zs : tuple α p}
variables {ws : tuple α q}
lemma ex6 : p = m + n  → zs == xs ++ ys →  zs ++ ws == xs ++ (ys ++ ws) :=
by blast

def ex : p = n + m  → zs == xs ++ ys →  zs ++ ws == xs ++ (ys ++ ws) :=
by blast
end tuple

end foo
