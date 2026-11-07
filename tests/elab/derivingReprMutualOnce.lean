/-!
`deriving Repr` on a mutual block generates one block of auxiliary functions for the whole block
instead of one per type, and still names each instance after its own type.
-/

/--
trace: [Elab.Deriving.repr]
    [mutual
       @[no_expose✝]
       partial def instReprA.repr_1 (x✝ : @A✝) (prec✝ : Nat✝) : Format✝ :=
         let localinst✝ : Repr✝ (@A✝) := ⟨instReprA.repr_1⟩;
         let localinst✝¹ : Repr✝ (@B✝) := ⟨instReprA.repr_2⟩;
         match x✝ with
         | @A.a a✝ =>
           Repr.addAppParen✝
             (Format.group✝
               (Format.nest✝ (if prec✝ ≥ max_prec then 1 else 2) (Format.text✝ "A.a" ++ Format.line✝ ++ reprArg✝ a✝)))
             prec✝
         | @A.leaf =>
           Repr.addAppParen✝ (Format.group✝ (Format.nest✝ (if prec✝ ≥ max_prec then 1 else 2) (Format.text✝ "A.leaf")))
             prec✝
       @[no_expose✝]
       partial def instReprA.repr_2 (x✝¹ : @B✝) (prec✝ : Nat✝) : Format✝ :=
         let localinst✝² : Repr✝ (@A✝) := ⟨instReprA.repr_1⟩;
         let localinst✝³ : Repr✝ (@B✝) := ⟨instReprA.repr_2⟩;
         match x✝¹ with
         | @B.b a✝¹ =>
           Repr.addAppParen✝
             (Format.group✝
               (Format.nest✝ (if prec✝ ≥ max_prec then 1 else 2) (Format.text✝ "B.b" ++ Format.line✝ ++ reprArg✝ a✝¹)))
             prec✝
         | @B.leaf =>
           Repr.addAppParen✝ (Format.group✝ (Format.nest✝ (if prec✝ ≥ max_prec then 1 else 2) (Format.text✝ "B.leaf")))
             prec✝
     end,
     instance instReprA : Repr✝ (@A✝) :=
       ⟨instReprA.repr_1⟩,
     instance instReprB : Repr✝ (@B✝) :=
       ⟨instReprA.repr_2⟩]
-/
#guard_msgs (whitespace := lax) in
set_option trace.Elab.Deriving.repr true in
mutual
inductive A where
  | a (b : B)
  | leaf
  deriving Repr
inductive B where
  | b (a : A)
  | leaf
  deriving Repr
end

/-- info: A.a (B.b (A.leaf)) -/
#guard_msgs in #eval A.a (.b .leaf)

/-- info: B.b (A.a (B.leaf)) -/
#guard_msgs in #eval B.b (.a .leaf)

example : Repr A := instReprA
example : Repr B := instReprB

/-! Types from different mutual blocks in one `deriving instance` command. -/

mutual
inductive C where
  | c (d : D)
  | leaf
inductive D where
  | d (c : C)
  | leaf
end

inductive E where
  | e (n : Nat)

deriving instance Repr for C, E, D

/-- info: C.c (D.d (C.leaf)) -/
#guard_msgs in #eval C.c (.d .leaf)

/-- info: D.d (C.c (D.leaf)) -/
#guard_msgs in #eval D.d (.c .leaf)

/-- info: E.e 3 -/
#guard_msgs in #eval E.e 3

example : Repr C := instReprC
example : Repr D := instReprD
example : Repr E := instReprE
