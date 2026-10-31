/-! We need to execute `csimp` both before and after `macr_inline` -/

@[macro_inline]
def myLength (xs : List Nat) : Nat := xs.length

/--
trace: [Compiler.init] size: 1
    def myLengthTest xs : Nat :=
      let _x.1 := @List.lengthTR _ xs;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.init true in
def myLengthTest (xs : List Nat) : Nat := myLength xs

@[noinline]
def myIte (c : Bool) (t e : Nat) : Nat := if c then t else e

@[macro_inline]
def myIte' (c : Bool) (t e : Nat) : Nat := if c then t else e

@[csimp]
theorem myIteThm : @myIte = @myIte' := rfl

/--
trace: [Compiler.init] size: 8
    def myIteTest c t e : Nat :=
      let _x.1 := true;
      let _x.2 := Bool.decEq c _x.1;
      let _x.3 := _x.2 # 0;
      cases _x.3 : Nat
      | Bool.false =>
        let _x.4 := Nat.add e e;
        return _x.4
      | Bool.true =>
        let _x.5 := Nat.add t t;
        return _x.5
-/
#guard_msgs in
set_option trace.Compiler.init true in
def myIteTest (c : Bool) (t e : Nat) : Nat := myIte c (Nat.add t t) (Nat.add e e)

section Error

def List.myGetD (x : List α) (i : Nat) (dflt : α) : α :=
  match x, i with
  | [], _ => dflt
  | a :: _, 0 => a
  | _ :: t, k + 1 => t.myGetD k dflt

def List.myGetD' (x : List α) (i : Nat) (dflt : α) : α :=
  match x, i with
  | [], _ => dflt
  | a :: _, 0 => a
  | _ :: t, k + 1 => t.myGetD' k dflt
termination_by x

@[csimp] theorem List.myGetD_eq_myGetD' : @myGetD = @myGetD' := by
  funext α x i dflt; fun_induction myGetD <;> simp_all [myGetD']

def myGetter (i : Nat) : [Bool, Nat, Int → Nat].myGetD i Unit :=
  match i with
  | 0 => true
  | 1 => (3 : Nat)
  | 2 => fun i => i.natAbs
  | _ + 3 => ()

-- used to error: function expected: @this i
def test (i : Int) : Nat :=
  have := myGetter 2
  this i

end Error

section Chain

@[noinline]
def fun6 (n : Nat) := n

@[macro_inline]
def fun5 (n : Nat) := fun6 n

@[noinline]
def fun4 (n : Nat) := n

@[macro_inline]
def fun3 (n : Nat) := fun4 n

@[noinline]
def fun2 (n : Nat) := n

@[macro_inline]
def fun1 (n : Nat) := fun2 n

@[csimp]
theorem t1 : fun2 = fun3 := by rfl

@[csimp]
theorem t2 : fun4 = fun5 := by rfl

/--
trace: [Compiler.init] size: 1
    def testMe n : Nat :=
      let _x.1 := fun6 n;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.init true in
def testMe (n : Nat) := fun1 n

end Chain
