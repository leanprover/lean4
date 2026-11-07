/-!
`deriving BEq` on a mutual block generates one block of auxiliary functions for the whole block
instead of one per type, and still names each instance after its own type.
-/

/--
trace: [Elab.Deriving.beq]
    [mutual
       set_option match.ignoreUnusedAlts✝ true
       partial def instBEqA.beq_1 (x✝ : @A✝) (x✝¹ : @A✝) : Bool✝ :=
         let localinst✝ : BEq✝ (@A✝) := ⟨instBEqA.beq_1⟩;
         let localinst✝¹ : BEq✝ (@B✝) := ⟨instBEqA.beq_2⟩;
         match x✝, x✝¹ with
         | @A.a a✝, @A.a b✝ => a✝ == b✝
         | @A.leaf, @A.leaf => true✝
         | _, _ => false✝
       partial def instBEqA.beq_2 (x✝² : @B✝) (x✝³ : @B✝) : Bool✝ :=
         let localinst✝² : BEq✝ (@A✝) := ⟨instBEqA.beq_1⟩;
         let localinst✝³ : BEq✝ (@B✝) := ⟨instBEqA.beq_2⟩;
         match x✝², x✝³ with
         | @B.b a✝¹, @B.b b✝¹ => a✝¹ == b✝¹
         | @B.leaf, @B.leaf => true✝
         | _, _ => false✝
     end,
     instance instBEqA : BEq✝ (@A✝) :=
       ⟨instBEqA.beq_1⟩,
     instance instBEqB : BEq✝ (@B✝) :=
       ⟨instBEqA.beq_2⟩]
-/
#guard_msgs (whitespace := lax) in
set_option trace.Elab.Deriving.beq true in
mutual
inductive A where
  | a (b : B)
  | leaf
  deriving BEq
inductive B where
  | b (a : A)
  | leaf
  deriving BEq
end

#guard A.a (.b .leaf) == A.a (.b .leaf)
#guard A.a (.b .leaf) != A.a .leaf
#guard B.b (.a .leaf) == B.b (.a .leaf)
#guard B.b (.a .leaf) != B.leaf

example : BEq A := instBEqA
example : BEq B := instBEqB

/-! Types from different mutual blocks, and an enum, in one `deriving instance` command. -/

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

inductive F where
  | x | y

deriving instance BEq for C, E, F, D

#guard C.c (.d .leaf) == C.c (.d .leaf)
#guard C.c (.d .leaf) != C.leaf
#guard D.d (.c .leaf) == D.d (.c .leaf)
#guard E.e 3 == E.e 3
#guard E.e 3 != E.e 4
#guard F.x == F.x
#guard F.x != F.y

example : BEq C := instBEqC
example : BEq D := instBEqD
example : BEq E := instBEqE
example : BEq F := instBEqF
