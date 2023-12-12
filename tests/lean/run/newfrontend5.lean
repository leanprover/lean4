def foo {α} (f : {β : Type _} → β → β) (a : α) : α :=
f a

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
#check foo @(fun β b => b) true -- works
#check_failure foo @(fun b => b) true     -- fails as expected, and error message is clear
#check foo @(fun β b => b) true   -- works (implicit lambdas were disabled)


set_option pp.all true

-- The following test got stuck at universe constraints after if fixed the `decAux?` bug.
-- #check let x := (fun f => (f, f)) @id; (x.1 (), x.2 true) -- works
-- #check_failure let x := (fun f => (f, f)) id; (x.1 (), x.2 true) -- fails as expected

set_option pp.all false
set_option pp.explicit true

def h (x := 10) (y := 20) : Nat := x + y
#check h -- h 10 20 : Nat
#check let f := @h; f -- (let f : optParam Nat 10 → optParam Nat 20 → Nat := @h; f 10 20) : Nat

#check let f := fun (x : optParam Nat 10) => x + 1; f + f 1
#check (fun (x : optParam Nat 10) => x)

#check let_fun x := 10; x + 1
