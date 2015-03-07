import data.nat logic

open bool nat

check
 show nat → bool
 | 0     := tt
 | (n+1) := ff

definition mult : nat → nat → nat :=
have plus : nat → nat → nat
| 0        b := b
| (succ a) b := succ (plus a b),
have mult : nat → nat → nat
| 0        b := 0
| (succ a) b := plus (mult a b) b,
mult

print definition mult

example : mult 3 7 = 21 := rfl

example : mult 8 7 = 56 := rfl

theorem add_eq_addl : ∀ x y, x + y = x ⊕ y
| 0        0     := rfl
| (succ x) 0     :=
  begin
    have addl_z : ∀ a : nat, a ⊕ 0 = a
    | 0        := rfl
    | (succ a) := calc
          (succ a) ⊕ 0 = succ (a ⊕ 0) : rfl
                   ... = succ a       : addl_z,
    rewrite addl_z
  end
| 0     (succ y) :=
  begin
    have z_add : ∀ a : nat, 0 + a = a
    | 0        := rfl
    | (succ a) :=
      begin
        rewrite ▸ succ(0 + a) = _,
        rewrite z_add
      end,
    rewrite z_add
  end
| (succ x) (succ y) :=
  begin
    change (succ x + succ y = succ (x ⊕ succ y)),
    have s_add : ∀ a b : nat, succ a + b = succ (a + b)
    | 0        0        := rfl
    | (succ a) 0        := rfl
    | 0        (succ b) :=
      begin
        change (succ (succ 0 + b) = succ (succ (0 + b))),
        rewrite -(s_add 0 b)
      end
    | (succ a) (succ b) :=
       begin
         change (succ (succ (succ a) + b) = succ (succ (succ a + b))),
         apply (congr_arg succ),
         rewrite (s_add (succ a) b),
       end,
    rewrite [s_add, add_eq_addl]
  end

print definition add_eq_addl
