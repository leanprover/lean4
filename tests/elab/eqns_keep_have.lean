/-!
Tests that equation lemmas keep the `have`s at the root of the right-hand side, also above a split
`match`, so that `vcgen +jp [f]` sees the join points of `f` (#16122).
-/
set_option linter.unusedVariables false

def f (x : Nat) : Nat :=
  have y := x + 1
  y + y

/--
info: f.eq_1 (x : Nat) :
  f x =
    have y := x + 1;
    y + y
-/
#guard_msgs in #check f.eq_1

-- A join point of `do` notation.
def prog2 (b : Nat → Bool) : StateM Nat Unit := do
  if b 0 then modify (· + 1) else modify (· + 2)
  if b 1 then modify (· + 1) else modify (· + 2)

/--
info: prog2.eq_1 (b : Nat → Bool) :
  prog2 b =
    have __do_jp := fun __r => if b 1 = true then modify fun x => x + 1 else modify fun x => x + 2;
    if b 0 = true then do
      let __r ← modify fun x => x + 1
      __do_jp __r
    else do
      let __r ← modify fun x => x + 2
      __do_jp __r
-/
#guard_msgs in #check prog2.eq_1

-- The `have` stays above the split `match`, and is dropped where it is unused.
def h (x : Option Nat) : Nat :=
  have y := 1
  have z := y + 1
  match x with
  | some v => v + z + z
  | none => y

/--
info: h.eq_1 (v : Nat) :
  h (some v) =
    have y := 1;
    have z := y + 1;
    v + z + z
-/
#guard_msgs in #check h.eq_1

/--
info: h.eq_2 :
  h none =
    have y := 1;
    y
-/
#guard_msgs in #check h.eq_2

-- The join point of `do` stays above the split `match` and the `if`.
def rootMatch (x : Nat) (b : Bool) : StateM Nat Nat := do
  let mut y := 0
  match x with
  | 0 => y := 1
  | _ + 1 => if b then y := 2 else y := 3
  let s ← get
  return y + s

/--
info: rootMatch.eq_2 (b : Bool) (n : Nat) :
  rootMatch n.succ b =
    have __do_jp := fun __r y => do
      let s ← get
      pure (y + s);
    if b = true then
      have y := 2;
      __do_jp () y
    else
      have y := 3;
      __do_jp () y
-/
#guard_msgs in #check rootMatch.eq_2

-- Nested join points.
def seqIfs (x : Nat) (b c : Bool) : StateM Nat Nat := do
  let mut y := 0
  match x with
  | 0 => y := 1
  | _ + 1 => if b then y := 2 else y := 3
  if c then y := y + 1
  let s ← get
  return y + s

/--
info: seqIfs.eq_2 (b c : Bool) (n : Nat) :
  seqIfs n.succ b c =
    have __do_jp := fun __r y =>
      have __do_jp := fun __r y => do
        let s ← get
        pure (y + s);
      if c = true then
        have y := y + 1;
        __do_jp () y
      else __do_jp () y;
    if b = true then
      have y := 2;
      __do_jp () y
    else
      have y := 3;
      __do_jp () y
-/
#guard_msgs in #check seqIfs.eq_2

-- Zeta-reducing chained `have`s would be exponential.
def chain (f : Nat → Nat) (x : Option Nat) : Nat :=
  have p := f 0
  have q := p + p
  have r := q + q
  match x with
  | some a => r + a
  | none => 0

/--
info: chain.eq_1 (f : Nat → Nat) (a : Nat) :
  chain f (some a) =
    have p := f 0;
    have q := p + p;
    have r := q + q;
    r + a
-/
#guard_msgs in #check chain.eq_1

-- The value of the `have` depends on the discriminant.
def dep (x : Nat) : Nat :=
  have y := x + 1
  match x with
  | 0 => y
  | n + 1 => n + y

/--
info: dep.eq_2 (n : Nat) :
  dep n.succ =
    have y := n.succ + 1;
    n + y
-/
#guard_msgs in #check dep.eq_2

-- A dependent `let` stays a `let`.
def depLet (x : Nat) : Fin 5 :=
  let n := 4
  match x with
  | 0 => (⟨n, by decide⟩ : Fin (n + 1))
  | _ + 1 => 0

/--
info: depLet.eq_1 :
  depLet 0 =
    let n := 4;
    ⟨n, depLet._proof_1⟩
-/
#guard_msgs in #check depLet.eq_1

-- The `have` is zeta-reduced if it is a discriminant.
def discr (x : Nat) : Nat :=
  have y := x
  match y with
  | 0 => 1
  | n + 1 => n

/-- info: discr.eq_2 (n : Nat) : discr n.succ = n -/
#guard_msgs in #check discr.eq_2

def discr2 (x : Nat) : Nat :=
  have k := x + 2
  match x, k with
  | 0, _ => 1
  | n + 1, m => n + m

/-- info: discr2.eq_2 (n : Nat) : discr2 n.succ = n + (n.succ + 2) -/
#guard_msgs in #check discr2.eq_2

-- The `match` in the value of the `have` is split, and the `have` is kept.
def inValue (x : Option Nat) : Nat :=
  have y := match x with
    | some a => a
    | none => 0
  y + 1

/--
info: inValue.eq_1 (a : Nat) :
  inValue (some a) =
    have y := a;
    y + 1
-/
#guard_msgs in #check inValue.eq_1

-- Structural and well-founded recursion.
def srec (f : Nat → Nat) (n : Nat) : Nat :=
  have v := f n
  match n with
  | 0 => v + v
  | m + 1 => srec f m + v + v

/--
info: srec.eq_2 (f : Nat → Nat) (n_1 : Nat) :
  srec f n_1.succ =
    have v := f n_1.succ;
    srec f n_1 + v + v
-/
#guard_msgs in #check srec.eq_2

def wrec (f : Nat → Nat) (n : Nat) : Nat :=
  have v := f n
  match n with
  | 0 => v + v
  | m + 1 => wrec f (m / 2) + v + v
termination_by n
decreasing_by grind

/--
info: wrec.eq_2 (f : Nat → Nat) (n_1 : Nat) :
  wrec f n_1.succ =
    have v := f n_1.succ;
    wrec f (n_1 / 2) + v + v
-/
#guard_msgs in #check wrec.eq_2

-- A `have` in a `match` alternative.
def k (x : Option Nat) : Nat :=
  match x with
  | some a => have y := a + 1; y * y
  | none => 0

/--
info: k.eq_1 (a : Nat) :
  k (some a) =
    have y := a + 1;
    y * y
-/
#guard_msgs in #check k.eq_1

-- Structural recursion.
def r : Nat → Nat
  | 0 => 0
  | n + 1 => have y := r n; y + y

/--
info: r.eq_2 (n : Nat) :
  r n.succ =
    have y := r n;
    y + y
-/
#guard_msgs in #check r.eq_2

-- Well-founded recursion.
def w (n : Nat) : Nat := if n = 0 then 0 else have y := w (n - 1); y + y
termination_by n

/--
info: w.eq_1 (n : Nat) :
  w n =
    if n = 0 then 0
    else
      have y := w (n - 1);
      y + y
-/
#guard_msgs in #check w.eq_1

-- A `have` with a constructor value is inlined as a discriminant, so the `match` reduces.
def ctorLet (x : Nat) : Nat :=
  have y := some x
  match y with
  | none => 42
  | some n =>
    match n with
    | 0 => 0
    | m + 1 => m

/-- info: ctorLet.eq_2 (n : Nat) : ctorLet n.succ = n -/
#guard_msgs in #check ctorLet.eq_2

-- The value of the `have` has the `match` below a nested `have`.
def nestedLet (x : Nat) : Nat :=
  have y :=
    have z := x
    match z with
    | 0 => 42
    | n + 1 => n
  y

/--
info: nestedLet.eq_2 (n : Nat) :
  nestedLet n.succ =
    have y := n;
    y
-/
#guard_msgs in #check nestedLet.eq_2

-- The constructor value is reached through an alias.
def ctorAlias (x : Nat) : Nat :=
  have y := some x
  have z := y
  match z with
  | none => 42
  | some n =>
    match n with
    | 0 => 0
    | m + 1 => m

/-- info: ctorAlias.eq_1 : ctorAlias 0 = 0 -/
#guard_msgs in #check ctorAlias.eq_1


/-- info: ctorAlias.eq_2 (n : Nat) : ctorAlias n.succ = n -/
#guard_msgs in #check ctorAlias.eq_2

def g (n : Nat) : Option Nat := if n = 0 then none else some n

-- An unused `have` is dropped, also above a `match` that is not split.
def unusedRoot (x : Nat) : Nat :=
  have k := x + 1
  match g x with
  | some a => a
  | none => 0

/--
info: unusedRoot.eq_1 (x : Nat) :
  unusedRoot x =
    match g x with
    | some a => a
    | none => 0
-/
#guard_msgs in #check unusedRoot.eq_1

-- Also inside a split branch.
def unusedBranch (x : Nat) (y : Option Nat) : Nat :=
  match y with
  | some b =>
    have k := b + 1
    match g x with
    | some a => a
    | none => 0
  | none => 0

/--
info: unusedBranch.eq_1 (x a : Nat) :
  unusedBranch x (some a) =
    match g x with
    | some a => a
    | none => 0
-/
#guard_msgs in #check unusedBranch.eq_1

-- Splitting `x` exposes a `match` in the value of `c`, which must then be split too. The outer
-- `match` generalizes the `have`s, whose values depend on `x`, so the `match x` in the value of `a`
-- is split first, and the outer `match` then reduces.
def nestedValueCases (x : Nat) : Nat :=
  have a :=
    have b := x + 1
    match x with
    | 0 => b
    | n + 1 => b + (match n with | 0 => 10 | m + 1 => m)
  have c := a + a
  match x with
  | 0 => c
  | n + 1 => c + n


/--
info: nestedValueCases.eq_1 :
  nestedValueCases 0 =
    have a := 0 + 1;
    have c := a + a;
    c
-/
#guard_msgs in #check nestedValueCases.eq_1

/--
info: nestedValueCases.eq_3 (n_1 : Nat) :
  nestedValueCases n_1.succ.succ =
    have a := n_1.succ.succ + 1 + n_1;
    have c := a + a;
    c + n_1.succ
-/
#guard_msgs in #check nestedValueCases.eq_3

-- The target reaches the `match` in the value of `c` only through `d`.
def nestedValueChain (x : Nat) : Nat :=
  have a :=
    have b := x + 1
    match x with
    | 0 => b
    | n + 1 => b + (match n with | 0 => 10 | m + 1 => m)
  have c := a + a
  have d := c + c
  match x with
  | 0 => d
  | n + 1 => d + n

/--
info: nestedValueChain.eq_3 (n_1 : Nat) :
  nestedValueChain n_1.succ.succ =
    have a := n_1.succ.succ + 1 + n_1;
    have c := a + a;
    have d := c + c;
    d + n_1.succ
-/
#guard_msgs in #check nestedValueChain.eq_3

-- Literal patterns overlap: the `match` in the value is simplified with the hypotheses of the split.
def valNatLit (x : Nat) : Nat :=
  have y := match x with
    | 5 => 1
    | 7 => 3
    | _ => 2
  y + y
/--
info: equations:
@[backward_defeq] theorem valNatLit.eq_1 : valNatLit 5 =
  have y := 1;
  y + y
@[backward_defeq] theorem valNatLit.eq_2 : valNatLit 7 =
  have y := 3;
  y + y
theorem valNatLit.eq_3 : ∀ (x : Nat),
  (x = 5 → False) →
    (x = 7 → False) →
      valNatLit x =
        have y := 2;
        y + y
-/
#guard_msgs in #print equations valNatLit

-- The `match`es in the values are split in the order in which they occur in the right-hand side.
def twoVals (x z : Nat) : Nat :=
  have a := match x with
    | 0 => 1
    | _ + 1 => 2
  have b := match z with
    | 0 => a
    | _ + 1 => a + 1
  b + b
/--
info: equations:
@[backward_defeq] theorem twoVals.eq_1 : twoVals 0 0 =
  have a := 1;
  have b := a;
  b + b
@[backward_defeq] theorem twoVals.eq_2 : ∀ (n : Nat),
  twoVals n.succ 0 =
    have a := 2;
    have b := a;
    b + b
@[backward_defeq] theorem twoVals.eq_3 : ∀ (n : Nat),
  twoVals 0 n.succ =
    have a := 1;
    have b := a + 1;
    b + b
@[backward_defeq] theorem twoVals.eq_4 : ∀ (n n_1 : Nat),
  twoVals n_1.succ n.succ =
    have a := 2;
    have b := a + 1;
    b + b
-/
#guard_msgs in #print equations twoVals

-- Overlapping patterns in a value.
def valOverlap (x y : Nat) : Nat :=
  have r := match x, y with
    | 0, _ => 1
    | _, 0 => 2
    | n + 1, m + 1 => n + m
  r + r
/--
info: equations:
@[backward_defeq] theorem valOverlap.eq_1 : ∀ (y : Nat),
  valOverlap 0 y =
    have r := 1;
    r + r
theorem valOverlap.eq_2 : ∀ (x : Nat),
  (x = 0 → False) →
    valOverlap x 0 =
      have r := 2;
      r + r
@[backward_defeq] theorem valOverlap.eq_3 : ∀ (n m : Nat),
  valOverlap n.succ m.succ =
    have r := n + m;
    r + r
-/
#guard_msgs in #print equations valOverlap

-- A `match` in a value whose discriminants are not all variables.
def valMixedDiscr (x : Nat) : Nat :=
  have y := match x, x + 1 with
    | 0, _ => 1
    | n + 1, m => n + m
  y + y
/--
info: equations:
@[backward_defeq] theorem valMixedDiscr.eq_1 : valMixedDiscr 0 =
  have y := 1;
  y + y
@[backward_defeq] theorem valMixedDiscr.eq_2 : ∀ (n : Nat),
  valMixedDiscr n.succ =
    have y := n + (n.succ + 1);
    y + y
-/
#guard_msgs in #print equations valMixedDiscr

-- The same variable is matched in a value and in the right-hand side.
def valAndTarget (x : Nat) : Nat :=
  have y := match x with
    | 0 => 1
    | _ + 1 => 2
  match x with
  | 0 => y + y
  | n + 1 => y + n
/--
info: equations:
@[backward_defeq] theorem valAndTarget.eq_1 : valAndTarget 0 = 1 + 1
@[backward_defeq] theorem valAndTarget.eq_2 : ∀ (n : Nat), valAndTarget n.succ = 2 + n
-/
#guard_msgs in #print equations valAndTarget

-- Structural recursion through a `match` in a value.
def listVal (xs : List Nat) : Nat :=
  have r := match xs with
    | [] => 0
    | x :: ys => x + listVal ys
  r + r
/--
info: equations:
@[backward_defeq] theorem listVal.eq_1 : listVal [] =
  have r := 0;
  r + r
@[backward_defeq] theorem listVal.eq_2 : ∀ (x : Nat) (ys : List Nat),
  listVal (x :: ys) =
    have r := x + listVal ys;
    r + r
-/
#guard_msgs in #print equations listVal

-- Well-founded recursion through a `match` in a value.
def wfVal (n : Nat) : Nat :=
  have r := match n with
    | 0 => 0
    | m + 1 => wfVal (m / 2)
  r + r
termination_by n
decreasing_by grind
/--
info: equations:
@[backward_defeq] theorem wfVal.eq_1 : wfVal 0 =
  have r := 0;
  r + r
theorem wfVal.eq_2 : ∀ (n_1 : Nat),
  wfVal n_1.succ =
    have r := wfVal (n_1 / 2);
    r + r
-/
#guard_msgs in #print equations wfVal

inductive Vec (α : Type) : Nat → Type
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

-- Indexed discriminants in a value.
def vecTwo (n : Nat) (v w : Vec Nat n) : Nat :=
  have r := match v, w with
    | .nil, .nil => 0
    | .cons a _, .cons b _ => match a with
      | 0 => b
      | k + 1 => k + b
  r + r
/--
info: equations:
@[backward_defeq] theorem vecTwo.eq_1 : vecTwo 0 Vec.nil Vec.nil =
  have r := 0;
  r + r
@[backward_defeq] theorem vecTwo.eq_2 : ∀ (n_2 : Nat) (a_1 : Vec Nat n_2) (b : Nat) (a_2 : Vec Nat n_2),
  vecTwo (n_2 + 1) (Vec.cons 0 a_1) (Vec.cons b a_2) =
    have r := b;
    r + r
@[backward_defeq] theorem vecTwo.eq_3 : ∀ (n_2 : Nat) (a_1 : Vec Nat n_2) (b : Nat) (a_2 : Vec Nat n_2) (n : Nat),
  vecTwo (n_2 + 1) (Vec.cons n.succ a_1) (Vec.cons b a_2) =
    have r := n + b;
    r + r
-/
#guard_msgs in #print equations vecTwo

-- `y` is inlined as a discriminant, since `match y` then reduces. `big` is not, since
-- `match g w, big` does not reduce.
def ctorDiscrIrrelevant (x w : Nat) : Nat :=
  have big := some (x * x + x * x)
  have y := some x
  (match y with
   | some n => n
   | none => 0) +
  (match g w, big with
   | some a, some k => a + k
   | _, _ => 0) +
  (match g w, big with
   | some a, some k => a - k
   | _, _ => big.get!)

/--
info: equations:
@[backward_defeq] theorem ctorDiscrIrrelevant.eq_1 : ∀ (x w : Nat),
  ctorDiscrIrrelevant x w =
    have big := some (x * x + x * x);
    (x +
        match g w, big with
        | some a, some k => a + k
        | x, x_1 => 0) +
      match g w, big with
      | some a, some k => a - k
      | x, x_1 => big.get!
-/
#guard_msgs in #print equations ctorDiscrIrrelevant

-- The `match` has the index `n + 1` as a discriminant, which `simpMatch?` reduces.
def ctorDiscrIndexed (n a : Nat) (v w : Vec Nat n) : Nat :=
  have p := Vec.cons a v
  have q := Vec.cons a w
  match p, q with
  | .cons b _, .cons c _ => b + c

/--
info: equations:
@[backward_defeq] theorem ctorDiscrIndexed.eq_1 : ∀ (n a : Nat) (v w : Vec Nat n), ctorDiscrIndexed n a v w = a + a
-/
#guard_msgs in #print equations ctorDiscrIndexed


def haveNested (x y : Nat) :=
  have a := y + y + y
  have a' := a + 1
  match x with
  | 0 =>
    have b := a + a
    b + b
  | _ =>
    have c := a' + a'
    have d := c
    c + c

/--
info: haveNested.eq_1 (y : Nat) :
  haveNested 0 y =
    have a := y + y + y;
    have b := a + a;
    b + b
-/
#guard_msgs in
#check haveNested.eq_1

/--
info: haveNested.eq_2 (x y : Nat) (x_3 : x = 0 → False) :
  haveNested x y =
    have a := y + y + y;
    have a' := a + 1;
    have c := a' + a';
    c + c
-/
#guard_msgs in
#check haveNested.eq_2

def bigHave (x : Nat) (y : Nat) : Nat :=
  have r := match x with
    | 0 => y + y * y + y^3
    | _ => y^4 + y^5 + y
  r + r + r

/--
info: bigHave.eq_1 (y : Nat) :
  bigHave 0 y =
    have r := y + y * y + y ^ 3;
    r + r + r
-/
#guard_msgs in #check bigHave.eq_1

/--
info: bigHave.eq_2 (x y : Nat) (x_3 : x = 0 → False) :
  bigHave x y =
    have r := y ^ 4 + y ^ 5 + y;
    r + r + r
-/
#guard_msgs in #check bigHave.eq_2
