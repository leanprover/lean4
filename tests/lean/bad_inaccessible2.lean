universe variables u
inductive vec (A : Type u) : nat → Type (max 1 u)
| nil {} : vec 0
| cons   : Π {n}, A → vec n → vec (n+1)

open vec

variables {A : Type u}
variables f : A → A → A

/- The following definition fails because the pattern variables are
   introduced in the following order:
         a va n b vb
   However, the type of va must be (vec A n). That is, it depends
   on a variable introduced after va.

   The error message is confusing.

   Alternatives:
   1- Ignore the problem since this is a very obscure use of inaccessible terms.
   2- Reorder variables based on their occurrence in inaccessible terms.
      If we do that, the variables in the pattern will be ordered as:
            n a va b vb
      and this example will work. This is not fully satisfactor since
      we can create another declaration where this heuristic is not the right
      solution.
   3- Produce a better error message.
-/
definition map_head : ∀ {n}, vec A n → vec A n → vec A n
| .(0)     nil nil                       := nil
| .(n+1) (@cons .(A) .(n) a va) (@cons .(A) n b vb) := cons (f a b) va
