open bool nat

-- set_option trace.compiler.code_gen true

attribute [reducible]
definition foo (b : bool) : Type₁ :=
cond b nat (nat → nat)

definition bla (b : bool) : foo b → nat :=
bool.cases_on b (λ f, f 100) (λ n, n)

definition of_dec (p : Prop) [h : decidable p] : bool :=
decidable.cases_on h (λ h, ff) (λ h, tt)

definition boo (n : nat) := bla (of_dec (n > 10))

definition x : nat := 20

definition tst (b : bool) (a : nat) : foo b :=
bool.cases_on b (λ n : nat, n * a) a

eval bla ff (λ n : nat, n+10)
eval bla tt x
eval boo 11 x
eval boo 9 (λ n : nat, n+20)
eval tst ff 4 10
eval tst tt 3
print "---------"
vm_eval bla ff (λ n : nat, n+10)
vm_eval bla tt x
vm_eval boo 11 x
vm_eval boo 9 (λ n : nat, n+20)
vm_eval tst ff 4 10
vm_eval tst tt 3
