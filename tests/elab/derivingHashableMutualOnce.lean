/-!
`deriving Hashable` on a mutual block generates one block of auxiliary functions for the whole
block instead of one per type, and still names each instance after its own type.
-/

/--
trace: [Elab.Deriving.hashable]
    [mutual
       partial def instHashableA.hash_1 (x✝ : @A✝) : UInt64✝ :=
         let localinst✝ : Hashable✝ (@A✝) := ⟨instHashableA.hash_1⟩;
         let localinst✝¹ : Hashable✝ (@B✝) := ⟨instHashableA.hash_2⟩;
         match x✝ with
         | @A.a a✝ => mixHash✝ 0 (instHashableA.hash_2 a✝)
         | @A.leaf => 1
       partial def instHashableA.hash_2 (x✝¹ : @B✝) : UInt64✝ :=
         let localinst✝² : Hashable✝ (@A✝) := ⟨instHashableA.hash_1⟩;
         let localinst✝³ : Hashable✝ (@B✝) := ⟨instHashableA.hash_2⟩;
         match x✝¹ with
         | @B.b a✝¹ => mixHash✝ 0 (instHashableA.hash_1 a✝¹)
         | @B.leaf => 1
     end,
     instance instHashableA : Hashable✝ (@A✝) :=
       ⟨instHashableA.hash_1⟩,
     instance instHashableB : Hashable✝ (@B✝) :=
       ⟨instHashableA.hash_2⟩]
-/
#guard_msgs (whitespace := lax) in
set_option trace.Elab.Deriving.hashable true in
mutual
inductive A where
  | a (b : B)
  | leaf
  deriving Hashable
inductive B where
  | b (a : A)
  | leaf
  deriving Hashable
end

#guard hash (A.a (.b .leaf)) == hash (A.a (.b .leaf))
#guard hash (A.a (.b .leaf)) != hash (A.a .leaf)
#guard hash (B.b (.a .leaf)) != hash B.leaf

example : Hashable A := instHashableA
example : Hashable B := instHashableB

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

deriving instance Hashable for C, E, D

#guard hash (C.c (.d .leaf)) == hash (C.c (.d .leaf))
#guard hash (D.d (.c .leaf)) != hash D.leaf
#guard hash (E.e 3) != hash (E.e 4)

example : Hashable C := instHashableC
example : Hashable D := instHashableD
example : Hashable E := instHashableE
