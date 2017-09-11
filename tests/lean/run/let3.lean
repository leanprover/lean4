definition p1 := (10, 20, 30)

definition v1 : nat :=
let (a, b, c) := p1 in
a + b + c

definition v2 : nat :=
let ⟨a, b, c⟩ := p1 in
a + b + c

example : v2 = 60 :=
rfl

/-
let with patterns is just syntax sugar for the match convoy pattern.

   let (a, b, c) := p1 in
   a + b + c

is encoded as

   match p1 with
   (a, b, c) := a + b + c
   end

One limitation is that the expexted type of the let-expression must be known.

TODO(Leo): improve visit_convoy in the elaborator, and remove this restriction.
-/

#eval
(let (a, b, c) := p1 in a + b : nat) -- We have to provide the type.

#eval
(let (a, b) := p1,
     (c, d) := b
 in c + d : nat)

definition v3 : nat :=
let (a, b) := p1,
    (c, d) := b
in c + d

example : v3 = 50 :=
rfl

#check
(let (a, b, c) := p1 in a + b : nat) -- We have to provide the type.

#reduce
(let (a, b, c) := p1 in a + b : nat) -- We have to provide the type.
