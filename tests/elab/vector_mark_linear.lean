/-!
Tests that vectors marked by `Vector.markLinear`, or by `Vector.propagateMark` from a marked
vector, are exempt from the optimizations that would share them: closed term extraction and common
subexpression elimination. Since `Vector` is represented by its underlying `Array` at runtime, the
marks bottom out in the `Array` primitives. Each test is paired with the unmarked version of the
same declaration, which is still optimized.
-/

/--
trace: [Compiler.extractClosed] size: 10
    def markedTable._closed_0 : Array Nat :=
      let _x.1 := 4;
      let _x.2 := 3;
      let _x.3 := 2;
      let _x.4 := 1;
      let _x.5 := 4;
      let _x.6 := Array.mkEmpty ◾ _x.5;
      let _x.7 := Array.push ◾ _x.6 _x.4;
      let _x.8 := Array.push ◾ _x.7 _x.3;
      let _x.9 := Array.push ◾ _x.8 _x.2;
      let _x.10 := Array.push ◾ _x.9 _x.5;
      return _x.10
[Compiler.extractClosed] size: 2
    def markedTable : Array Nat :=
      let _x.1 := markedTable._closed_0;
      let _x.2 := Array.markLinear ◾ _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.extractClosed true in
def markedTable : Vector Nat 4 := (#v[1, 2, 3, 4]).markLinear

/--
trace: [Compiler.extractClosed] size: 6
    def table : Array Nat :=
      let _x.1 := 4;
      let _x.2 := 1;
      let _x.3 := 2;
      let _x.4 := 3;
      let _x.5 := Array.mkEmpty ◾ _x.1;
      let _x.6 := markedTable._closed_0;
      return _x.6
-/
#guard_msgs in
set_option trace.Compiler.extractClosed true in
def table : Vector Nat 4 := #v[1, 2, 3, 4]

@[inline] def idA (n : Nat) : Nat := n
@[inline] def idB (n : Nat) : Nat := n

/--
trace: [Compiler.cse] size: 10
    def markedPair n : Vector Nat lcAny × Vector Nat lcAny :=
      let _x.1 := idA n;
      let _x.2 := 0;
      let _x.3 := instOfNatNat _x.2;
      let _x.4 := _x.3 # 0;
      let _x.5 := @Vector.replicate _ _x.1 _x.4;
      let _x.6 := @Vector.markLinear _ _x.1 _x.5;
      let _x.7 := idB n;
      let _x.8 := @Vector.replicate _ _x.7 _x.4;
      let _x.9 := @Vector.markLinear _ _x.7 _x.8;
      let _x.10 := @Prod.mk _ _ _x.6 _x.9;
      return _x.10
[Compiler.cse] size: 7
    def markedPair n : Vector Nat lcAny × Vector Nat lcAny :=
      let _x.1 := 0;
      let _x.2 := @Array.replicate _ n _x.1;
      let _x.3 := @Array.markLinear _ _x.2;
      let _x.4 := @Vector.mk _ n _x.3 ◾;
      let _x.5 := @Array.markLinear _ _x.2;
      let _x.6 := @Vector.mk _ n _x.5 ◾;
      let _x.7 := @Prod.mk _ _ _x.4 _x.6;
      return _x.7
[Compiler.cse] size: 5
    def markedPair n : Prod (Array Nat) (Array Nat) :=
      let _x.1 := 0;
      let _x.2 := Array.replicate ◾ n _x.1;
      let _x.3 := Array.markLinear ◾ _x.2;
      let _x.4 := Array.markLinear ◾ _x.2;
      let _x.5 := Prod.mk ◾ ◾ _x.3 _x.4;
      return _x.5
-/
#guard_msgs in
set_option trace.Compiler.cse true in
def markedPair (n : Nat) : Vector Nat (idA n) × Vector Nat (idB n) :=
  ((Vector.replicate (idA n) 0).markLinear, (Vector.replicate (idB n) 0).markLinear)

/--
trace: [Compiler.cse] size: 10
    def propagatedPair n xs : Vector Nat lcAny × Vector Nat lcAny :=
      let _x.1 := idA n;
      let _x.2 := 0;
      let _x.3 := instOfNatNat _x.2;
      let _x.4 := _x.3 # 0;
      let _x.5 := @Vector.replicate _ _x.1 _x.4;
      let _x.6 := @Vector.propagateMark n _x.1 _ _ xs _x.5;
      let _x.7 := idB n;
      let _x.8 := @Vector.replicate _ _x.7 _x.4;
      let _x.9 := @Vector.propagateMark n _x.7 _ _ xs _x.8;
      let _x.10 := @Prod.mk _ _ _x.6 _x.9;
      return _x.10
[Compiler.cse] size: 8
    def propagatedPair n xs : Vector Nat lcAny × Vector Nat lcAny :=
      let _x.1 := 0;
      let _x.2 := @Array.replicate _ n _x.1;
      let _x.3 := xs # 0;
      let _x.4 := @Array.propagateMark _ _ _x.3 _x.2;
      let _x.5 := @Vector.mk _ n _x.4 ◾;
      let _x.6 := @Array.propagateMark _ _ _x.3 _x.2;
      let _x.7 := @Vector.mk _ n _x.6 ◾;
      let _x.8 := @Prod.mk _ _ _x.5 _x.7;
      return _x.8
[Compiler.cse] size: 5
    def propagatedPair n xs : Prod (Array Nat) (Array Nat) :=
      let _x.1 := 0;
      let _x.2 := Array.replicate ◾ n _x.1;
      let _x.3 := Array.propagateMark ◾ ◾ xs _x.2;
      let _x.4 := Array.propagateMark ◾ ◾ xs _x.2;
      let _x.5 := Prod.mk ◾ ◾ _x.3 _x.4;
      return _x.5
-/
#guard_msgs in
set_option trace.Compiler.cse true in
def propagatedPair (xs : Vector Nat n) : Vector Nat (idA n) × Vector Nat (idB n) :=
  (xs.propagateMark (Vector.replicate (idA n) 0), xs.propagateMark (Vector.replicate (idB n) 0))

/--
trace: [Compiler.cse] size: 8
    def pair n : Vector Nat lcAny × Vector Nat lcAny :=
      let _x.1 := idA n;
      let _x.2 := 0;
      let _x.3 := instOfNatNat _x.2;
      let _x.4 := _x.3 # 0;
      let _x.5 := @Vector.replicate _ _x.1 _x.4;
      let _x.6 := idB n;
      let _x.7 := @Vector.replicate _ _x.6 _x.4;
      let _x.8 := @Prod.mk _ _ _x.5 _x.7;
      return _x.8
[Compiler.cse] size: 4
    def pair n : Vector Nat lcAny × Vector Nat lcAny :=
      let _x.1 := 0;
      let _x.2 := @Array.replicate _ n _x.1;
      let _x.3 := @Vector.mk _ n _x.2 ◾;
      let _x.4 := @Prod.mk _ _ _x.3 _x.3;
      return _x.4
[Compiler.cse] size: 3
    def pair n : Prod (Array Nat) (Array Nat) :=
      let _x.1 := 0;
      let _x.2 := Array.replicate ◾ n _x.1;
      let _x.3 := Prod.mk ◾ ◾ _x.2 _x.2;
      return _x.3
-/
#guard_msgs in
set_option trace.Compiler.cse true in
def pair (n : Nat) : Vector Nat (idA n) × Vector Nat (idB n) :=
  (Vector.replicate (idA n) 0, Vector.replicate (idB n) 0)
