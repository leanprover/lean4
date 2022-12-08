inductive KrivineInstruction
  | Access (n: Nat)
  | Grab (next: KrivineInstruction)
  | Push (next: KrivineInstruction) (continuation: KrivineInstruction)

inductive KrivineClosure
  | pair (i: KrivineInstruction) (e: List KrivineClosure)

namespace Ex1

def KrivineEnv := List KrivineClosure

-- We need to define a `SizeOf` instance for `KrivineEnv`. Otherwise, we cannot use the auto-generated well-founded relation in
-- recursive definitions.
noncomputable instance : SizeOf KrivineEnv := inferInstanceAs (SizeOf (List KrivineClosure))
-- We also need a `simp` theorem
@[simp] theorem KrivineEnv.sizeOf_spec (env : KrivineEnv) : sizeOf env = sizeOf (α := List KrivineClosure) env := rfl

-- It would be great to have a `deriving SizeOf` for definitions such as `KrivineEnv` above.

def KrivineEnv.depth (env : KrivineEnv) : Nat :=
  match env with
  | [] => 0
  | KrivineClosure.pair u e :: closures => Nat.max (1 + depth e) (depth closures)

end Ex1


namespace Ex2
-- Same example, but we use `abbrev` to define `KrivineEnv`. Thus, we inherit the `SizeOf` instance for `List`s.

abbrev KrivineEnv := List KrivineClosure

def KrivineEnv.depth (env : KrivineEnv) : Nat :=
  match env with
  | [] => 0
  | KrivineClosure.pair u e :: closures => Nat.max (1 + depth e) (depth closures)

end Ex2

namespace Ex3
-- Same example, but using `structure` instead of `def`

structure KrivineEnv where
  env : List KrivineClosure

def KrivineEnv.depth (env : KrivineEnv) : Nat :=
  match env with
  | { env := [] } => 0
  | { env := KrivineClosure.pair u e :: closures } => Nat.max (1 + depth { env := e }) (depth { env := closures })

end Ex3
