/-!
Tests that arrays marked by `Array.markLinear` are exempt from the optimizations that would share
them: closed term extraction and common subexpression elimination. Each test is paired with the
unmarked version of the same declaration, which is still optimized.
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
def markedTable : Array Nat := (#[1, 2, 3, 4]).markLinear

/--
trace: [Compiler.extractClosed] size: 6
    def table : Array Nat :=
      let _x.1 := 1;
      let _x.2 := 2;
      let _x.3 := 3;
      let _x.4 := 4;
      let _x.5 := Array.mkEmpty ◾ _x.4;
      let _x.6 := markedTable._closed_0;
      return _x.6
-/
#guard_msgs in
set_option trace.Compiler.extractClosed true in
def table : Array Nat := #[1, 2, 3, 4]

@[inline] def idA (n : Nat) : Nat := n
@[inline] def idB (n : Nat) : Nat := n

/--
trace: [Compiler.cse] size: 10
    def markedPair n : Array Nat × Array Nat :=
      let _x.1 := idA n;
      let _x.2 := 0;
      let _x.3 := instOfNatNat _x.2;
      let _x.4 := _x.3 # 0;
      let _x.5 := @Array.replicate _ _x.1 _x.4;
      let _x.6 := @Array.markLinear _ _x.5;
      let _x.7 := idB n;
      let _x.8 := @Array.replicate _ _x.7 _x.4;
      let _x.9 := @Array.markLinear _ _x.8;
      let _x.10 := @Prod.mk _ _ _x.6 _x.9;
      return _x.10
[Compiler.cse] size: 5
    def markedPair n : Array Nat × Array Nat :=
      let _x.1 := 0;
      let _x.2 := @Array.replicate _ n _x.1;
      let _x.3 := @Array.markLinear _ _x.2;
      let _x.4 := @Array.markLinear _ _x.2;
      let _x.5 := @Prod.mk _ _ _x.3 _x.4;
      return _x.5
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
def markedPair (n : Nat) : Array Nat × Array Nat :=
  ((Array.replicate (idA n) 0).markLinear, (Array.replicate (idB n) 0).markLinear)

/--
trace: [Compiler.cse] size: 8
    def pair n : Array Nat × Array Nat :=
      let _x.1 := idA n;
      let _x.2 := 0;
      let _x.3 := instOfNatNat _x.2;
      let _x.4 := _x.3 # 0;
      let _x.5 := @Array.replicate _ _x.1 _x.4;
      let _x.6 := idB n;
      let _x.7 := @Array.replicate _ _x.6 _x.4;
      let _x.8 := @Prod.mk _ _ _x.5 _x.7;
      return _x.8
[Compiler.cse] size: 3
    def pair n : Array Nat × Array Nat :=
      let _x.1 := 0;
      let _x.2 := @Array.replicate _ n _x.1;
      let _x.3 := @Prod.mk _ _ _x.2 _x.2;
      return _x.3
[Compiler.cse] size: 3
    def pair n : Prod (Array Nat) (Array Nat) :=
      let _x.1 := 0;
      let _x.2 := Array.replicate ◾ n _x.1;
      let _x.3 := Prod.mk ◾ ◾ _x.2 _x.2;
      return _x.3
-/
#guard_msgs in
set_option trace.Compiler.cse true in
def pair (n : Nat) : Array Nat × Array Nat :=
  (Array.replicate (idA n) 0, Array.replicate (idB n) 0)
