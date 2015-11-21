section
  parameter {A : Type}

  parameter A

  -- definition id (a : A) := a

  parameter {A}

  definition id₂ (a : A) := a
end

check @id
check @id₂

section
  parameters {A : Type} {B : Type}

  definition foo1 (a : A) (b : B) := a

  parameters {A} (B)

  definition foo2 (a : A) (b : B) := a

  parameters (A) {B}

  definition foo3 (a : A) (b : B) := a

  parameters (A) (B)

  definition foo4 (a : A) (b : B) := a

  check @foo1
  check @foo2
  check @foo3
  check @foo4
end

check @foo1
check @foo2
check @foo3
check @foo4

section
  variables {A : Type} {B : Type}

  definition boo1 (a : A) (b : B) := a

  variables {A} (B)

  definition boo2 (a : A) (b : B) := a

  variables (A) {B}

  definition boo3 (a : A) (b : B) := a

  variables (A) (B)

  definition boo4 (a : A) (b : B) := a

  check @boo1
  check @boo2
  check @boo3
  check @boo4
end

section
  variables {A : Type} {B : Type}

  parameter (A) -- ERROR
  variable (C)  -- ERROR
  variables (C) (D) -- ERROR
  variables C -- ERROR

  definition id3 (a : A) := a

  parameter id3 -- ERROR

  parameter (C : Type)

  variables {C}  -- ERROR

end
