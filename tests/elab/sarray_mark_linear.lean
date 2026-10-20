/-!
Tests that scalar arrays marked by `ByteArray.markLinear`/`FloatArray.markLinear` are exempt from
the optimizations that would share them: closed term extraction and common subexpression
elimination. Each test is paired with the unmarked version of the same declaration, which is still
optimized.
-/

/--
trace: [Compiler.extractClosed] size: 11
    def markedTable._closed_0 : ByteArray :=
      let _x.1 := 4;
      let _x.2 := 3;
      let _x.3 := 2;
      let _x.4 := 1;
      let _x.5 := 4;
      let _x.6 := Array.mkEmpty ◾ _x.5;
      let _x.7 := Array.push ◾ _x.6 _x.4;
      let _x.8 := Array.push ◾ _x.7 _x.3;
      let _x.9 := Array.push ◾ _x.8 _x.2;
      let _x.10 := Array.push ◾ _x.9 _x.1;
      let _x.11 := ByteArray.mk _x.10;
      return _x.11
[Compiler.extractClosed] size: 2
    def markedTable : ByteArray :=
      let _x.1 := markedTable._closed_0;
      let _x.2 := ByteArray.markLinear _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.extractClosed true in
def markedTable : ByteArray := (ByteArray.mk #[1, 2, 3, 4]).markLinear

/--
trace: [Compiler.extractClosed] size: 7
    def table : ByteArray :=
      let _x.1 := 1;
      let _x.2 := 2;
      let _x.3 := 3;
      let _x.4 := 4;
      let _x.5 := 4;
      let _x.6 := Array.mkEmpty ◾ _x.5;
      let _x.7 := markedTable._closed_0;
      return _x.7
-/
#guard_msgs in
set_option trace.Compiler.extractClosed true in
def table : ByteArray := ByteArray.mk #[1, 2, 3, 4]

@[inline] def idA (n : Nat) : Nat := n
@[inline] def idB (n : Nat) : Nat := n

/--
trace: [Compiler.cse] size: 7
    def markedPair n : FloatArray × FloatArray :=
      let _x.1 := idA n;
      let _x.2 := FloatArray.emptyWithCapacity _x.1;
      let _x.3 := FloatArray.markLinear _x.2;
      let _x.4 := idB n;
      let _x.5 := FloatArray.emptyWithCapacity _x.4;
      let _x.6 := FloatArray.markLinear _x.5;
      let _x.7 := @Prod.mk _ _ _x.3 _x.6;
      return _x.7
[Compiler.cse] size: 4
    def markedPair n : FloatArray × FloatArray :=
      let _x.1 := FloatArray.emptyWithCapacity n;
      let _x.2 := FloatArray.markLinear _x.1;
      let _x.3 := FloatArray.markLinear _x.1;
      let _x.4 := @Prod.mk _ _ _x.2 _x.3;
      return _x.4
[Compiler.cse] size: 4
    def markedPair n : Prod FloatArray FloatArray :=
      let _x.1 := FloatArray.emptyWithCapacity n;
      let _x.2 := FloatArray.markLinear _x.1;
      let _x.3 := FloatArray.markLinear _x.1;
      let _x.4 := Prod.mk ◾ ◾ _x.2 _x.3;
      return _x.4
-/
#guard_msgs in
set_option trace.Compiler.cse true in
def markedPair (n : Nat) : FloatArray × FloatArray :=
  ((FloatArray.emptyWithCapacity (idA n)).markLinear, (FloatArray.emptyWithCapacity (idB n)).markLinear)

/--
trace: [Compiler.cse] size: 5
    def pair n : FloatArray × FloatArray :=
      let _x.1 := idA n;
      let _x.2 := FloatArray.emptyWithCapacity _x.1;
      let _x.3 := idB n;
      let _x.4 := FloatArray.emptyWithCapacity _x.3;
      let _x.5 := @Prod.mk _ _ _x.2 _x.4;
      return _x.5
[Compiler.cse] size: 2
    def pair n : FloatArray × FloatArray :=
      let _x.1 := FloatArray.emptyWithCapacity n;
      let _x.2 := @Prod.mk _ _ _x.1 _x.1;
      return _x.2
[Compiler.cse] size: 2
    def pair n : Prod FloatArray FloatArray :=
      let _x.1 := FloatArray.emptyWithCapacity n;
      let _x.2 := Prod.mk ◾ ◾ _x.1 _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.cse true in
def pair (n : Nat) : FloatArray × FloatArray :=
  (FloatArray.emptyWithCapacity (idA n), FloatArray.emptyWithCapacity (idB n))
