structure Var : Type := (name : String)
instance Var.nameCoe : HasCoe String Var := ⟨Var.mk⟩

structure A : Type := (u : Unit)
structure B : Type := (u : Unit)

def a : A := A.mk ()
def b : B := B.mk ()

def Foo.chalk : A → List Var → Unit := λ _ _ => ()
def Bar.chalk : B → Unit := λ _ => ()

open Foo
open Bar

instance listCoe {α β} [HasCoe α β] : HasCoe (List α) (List β) :=
⟨fun as => as.map coe⟩

/- The following succeeds: -/
#check Foo.chalk a ["foo"] -- succeeds

/-
The following application fails, due to a curious interaction
between coercions and ad-hoc overloading.
-/
#check chalk a ["foo"] -- fails

/-
Note that the first argument clearly distinguishes the two
`chalk` applications, and there are no coercions in play for the first argument.

I am not arguing that we should support this case, merely logging that it surprised me,
and that I can not employ an otherwise desirable use of overloading because of it.

Note: it works if `Foo.chalk` takes `A` and `Var` and we pass `a` and `"foo"`.
-/

/-

Here is the analysis of why it doesn't work.
Given `chalk a ["foo"]` where `chalk` is overloaded,
the current elaborator performs the following steps:

1- Elaborate the arguments `a` and `["foo"]` without an expected
type. Thus, `["foo"]` is elaborated as a list of strings.

2- For each possible interpretation of `chalk`, we try to match the
arguments with the expected types. `Bar.chalk` fails because there is
no coercion from `A` to `B`. `Foo.chalk` fails because there is no
coercion from `List String` to `List Var`. Note that the example would
work if we had the coercion

```
instance listCoe {α β} [HasCoe α β] : HasCoe (List α) (List β) :=
⟨fun as => as.map coe⟩
```
However, users could still be surprised by the fact that the `chalk a ["foo"]` is
elaborated as `Foo.chalk a (coe ["foo"])` instead of `Foo.chalk a [coe "foo"]`.

Here are some alternative elaboration strategies I have considered.
We should discuss them in the next Dev meeting.

1- Instead of elaborating all arguments without an expected type, we
elaborate only the shortest argument prefix that is sufficient for
selecting the right overload candidate. Daniel's comments above
suggest this is the strategy he expected. It would fix this particular
instance, but it would still confuse users. For example, we can create
the alternative problem `chalk ["foo"] a`. Users could say "the second
argument clearly distinguishes the two applications."

2- Elaborate `chalk a ["foo"]` for each possible overload.  This is a
robust solution but may produce an exponential blowup. For example,
suppose we have `f_1 (f_2 (f_3 (f_4 ... (f_n a) ... )))` where all
`f_i` are overloaded. Moreover, every overload has the same result
type. Thus, we cannot prune the search space using the expected
type. This situation does not seem to occur in our code base.  It did
happen in Lean2, when we used to overload symbols such as `+` and `*`.
We should ask Reid how often overloads are used in mathlib, and
whether the exponential blowup is a real problem or not for them.

3- Use Lean3 approach, but when we get a typing error after we
selected the right overload candidate, we re-elaborate it using the
expected type instead of failing. This approach looks too haskish, and
it may still produce an exponential blowup.

I am inclined to (try to) use solution 2 in Lean4. We can have a
threshold on the amount of backtracking, and when it exceeds we
produce an error message stating all overloads that are generating
the huge search space.
-/
