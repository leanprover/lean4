def foo {α} (f : forall {β}, β → β) (a : α) : α :=
f a

new_frontend

#check_failure let g := id; foo g true -- fails
/-
Expands to
```
let g : ?γ → ?γ := @id ?γ;
@foo ?α (fun (β : Sort ?u) => g) true
```

Unification constraint
```
  ?γ → ?γ =?= β → β
```
fails because `β` is not in the scope of `?γ`

Error message can be improved because it doesn't make it clear
the issue is the scope of the metavariable. Not sure yet how to improve it.
-/
#check_failure (fun g => foo g 2) id -- fails for the same reason the previous one fail.

#check let g := @id; foo @g true -- works
/-
Expands into
```
let g : {γ : Sort ?v} → γ → γ := @id;
@foo ?α @g true
```
Note that `@g` also disables implicit lambdas.
The unification constraint is easily solved
```
{γ : Sort ?v} → γ → γ =?= {β : Sort ?u} → β → β
```
-/

#check foo id true  -- works
#check foo @id true -- works
#check foo (fun b => b) true -- works
#check foo (fun {β} b => b) true -- works
#check_failure foo @(fun b => b) true     -- fails as expected, and error message is clear
#check foo @(fun β b => b) true   -- works (implicit lambdas were disabled)
#check foo @(fun {β} b => b) true -- works (implicit lambdas were disabled)


set_option pp.all true

#check let x := (fun f => (f, f)) @id; (x.1 (), x.2 true) -- works
#check_failure let x := (fun f => (f, f)) id; (x.1 (), x.2 true) -- fails as expected
#check let x := (fun (f : {α : Type} → α → α) => (f, f)) @id; (x.1 (), x.2 true) -- works
