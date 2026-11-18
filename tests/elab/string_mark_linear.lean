/-!
Tests that strings marked by `String.markLinear` are exempt from the optimizations that would share
them: closed term extraction and common subexpression elimination. Each test is paired with the
unmarked version of the same declaration, which is still optimized.
-/

/--
trace: [Compiler.extractClosed] size: 3
    def markedGreeting._closed_0 : List UInt32 :=
      let _x.1 := [] ◾;
      let _x.2 := 105;
      let _x.3 := List.cons ◾ _x.2 _x.1;
      return _x.3
[Compiler.extractClosed] size: 3
    def markedGreeting._closed_1 : List UInt32 :=
      let _x.1 := markedGreeting._closed_0;
      let _x.2 := 104;
      let _x.3 := List.cons ◾ _x.2 _x.1;
      return _x.3
[Compiler.extractClosed] size: 2
    def markedGreeting._closed_2 : String :=
      let _x.1 := markedGreeting._closed_1;
      let _x.2 := String.ofList _x.1;
      return _x.2
[Compiler.extractClosed] size: 2
    def markedGreeting : String :=
      let _x.1 := markedGreeting._closed_2;
      let _x.2 := String.markLinear _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.extractClosed true in
def markedGreeting : String := (String.ofList ['h', 'i']).markLinear

/--
trace: [Compiler.extractClosed] size: 6
    def greeting : String :=
      let _x.1 := 104;
      let _x.2 := 105;
      let _x.3 := [] ◾;
      let _x.4 := markedGreeting._closed_0;
      let _x.5 := markedGreeting._closed_1;
      let _x.6 := markedGreeting._closed_2;
      return _x.6
-/
#guard_msgs in
set_option trace.Compiler.extractClosed true in
def greeting : String := String.ofList ['h', 'i']

@[inline] def idA (c : Char) : Char := c
@[inline] def idB (c : Char) : Char := c

/--
trace: [Compiler.cse] size: 7
    def markedPair s c : String × String :=
      let _x.1 := idA c;
      let _x.2 := String.push s _x.1;
      let _x.3 := String.markLinear _x.2;
      let _x.4 := idB c;
      let _x.5 := String.push s _x.4;
      let _x.6 := String.markLinear _x.5;
      let _x.7 := @Prod.mk _ _ _x.3 _x.6;
      return _x.7
[Compiler.cse] size: 4
    def markedPair s c : String × String :=
      let _x.1 := String.push s c;
      let _x.2 := String.markLinear _x.1;
      let _x.3 := String.markLinear _x.1;
      let _x.4 := @Prod.mk _ _ _x.2 _x.3;
      return _x.4
[Compiler.cse] size: 4
    def markedPair s c : Prod String String :=
      let _x.1 := String.push s c;
      let _x.2 := String.markLinear _x.1;
      let _x.3 := String.markLinear _x.1;
      let _x.4 := Prod.mk ◾ ◾ _x.2 _x.3;
      return _x.4
-/
#guard_msgs in
set_option trace.Compiler.cse true in
def markedPair (s : String) (c : Char) : String × String :=
  ((s.push (idA c)).markLinear, (s.push (idB c)).markLinear)

/--
trace: [Compiler.cse] size: 5
    def pair s c : String × String :=
      let _x.1 := idA c;
      let _x.2 := String.push s _x.1;
      let _x.3 := idB c;
      let _x.4 := String.push s _x.3;
      let _x.5 := @Prod.mk _ _ _x.2 _x.4;
      return _x.5
[Compiler.cse] size: 2
    def pair s c : String × String :=
      let _x.1 := String.push s c;
      let _x.2 := @Prod.mk _ _ _x.1 _x.1;
      return _x.2
[Compiler.cse] size: 2
    def pair s c : Prod String String :=
      let _x.1 := String.push s c;
      let _x.2 := Prod.mk ◾ ◾ _x.1 _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.cse true in
def pair (s : String) (c : Char) : String × String :=
  (s.push (idA c), s.push (idB c))
