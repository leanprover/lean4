namespace Arr

/--
trace: [Compiler.extractClosed] size: 18
    def Arr.arrayTable._closed_0 : Array Nat :=
      let _x.1 := 8;
      let _x.2 := 7;
      let _x.3 := 6;
      let _x.4 := 5;
      let _x.5 := 4;
      let _x.6 := 3;
      let _x.7 := 2;
      let _x.8 := 1;
      let _x.9 := 8;
      let _x.10 := Array.mkEmpty ◾ _x.9;
      let _x.11 := Array.push ◾ _x.10 _x.8;
      let _x.12 := Array.push ◾ _x.11 _x.7;
      let _x.13 := Array.push ◾ _x.12 _x.6;
      let _x.14 := Array.push ◾ _x.13 _x.5;
      let _x.15 := Array.push ◾ _x.14 _x.4;
      let _x.16 := Array.push ◾ _x.15 _x.3;
      let _x.17 := Array.push ◾ _x.16 _x.2;
      let _x.18 := Array.push ◾ _x.17 _x.9;
      return _x.18
[Compiler.extractClosed] size: 1
    def Arr.arrayTable : Array Nat :=
      let _x.1 := Arr.arrayTable._closed_0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.extractClosed true in
def arrayTable : Array Nat := #[1,2,3,4,5,6,7,8]

@[noinline]
def myid (x : α) := x

/--
trace: [Compiler.extractClosed] size: 2
    def Arr.nonTrivialArrayTable._closed_0 : Nat :=
      let _x.1 := 2;
      let _x.2 := Arr.myid._redArg _x.1;
      return _x.2
[Compiler.extractClosed] size: 2
    def Arr.nonTrivialArrayTable._closed_1 : Nat :=
      let _x.1 := 5;
      let _x.2 := Arr.myid._redArg _x.1;
      return _x.2
[Compiler.extractClosed] size: 2
    def Arr.nonTrivialArrayTable._closed_2 : Nat :=
      let _x.1 := 7;
      let _x.2 := Arr.myid._redArg _x.1;
      return _x.2
[Compiler.extractClosed] size: 18
    def Arr.nonTrivialArrayTable._closed_3 : Array Nat :=
      let _x.1 := 8;
      let _x.2 := Arr.nonTrivialArrayTable._closed_2;
      let _x.3 := 6;
      let _x.4 := Arr.nonTrivialArrayTable._closed_1;
      let _x.5 := 4;
      let _x.6 := 3;
      let _x.7 := Arr.nonTrivialArrayTable._closed_0;
      let _x.8 := 1;
      let _x.9 := 8;
      let _x.10 := Array.mkEmpty ◾ _x.9;
      let _x.11 := Array.push ◾ _x.10 _x.8;
      let _x.12 := Array.push ◾ _x.11 _x.7;
      let _x.13 := Array.push ◾ _x.12 _x.6;
      let _x.14 := Array.push ◾ _x.13 _x.5;
      let _x.15 := Array.push ◾ _x.14 _x.4;
      let _x.16 := Array.push ◾ _x.15 _x.3;
      let _x.17 := Array.push ◾ _x.16 _x.2;
      let _x.18 := Array.push ◾ _x.17 _x.9;
      return _x.18
[Compiler.extractClosed] size: 1
    def Arr.nonTrivialArrayTable : Array Nat :=
      let _x.1 := Arr.nonTrivialArrayTable._closed_3;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.extractClosed true in
def nonTrivialArrayTable : Array Nat := #[1,myid 2,3,4,myid 5,6,myid 7,8]

/--
trace: [Compiler.extractClosed] size: 10
    def Arr.dualArrayTable._closed_0 : Array Nat :=
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
[Compiler.extractClosed] size: 10
    def Arr.dualArrayTable._closed_1 : Array Nat :=
      let _x.1 := 7;
      let _x.2 := 6;
      let _x.3 := 5;
      let _x.4 := 4;
      let _x.5 := 4;
      let _x.6 := Array.mkEmpty ◾ _x.5;
      let _x.7 := Array.push ◾ _x.6 _x.5;
      let _x.8 := Array.push ◾ _x.7 _x.3;
      let _x.9 := Array.push ◾ _x.8 _x.2;
      let _x.10 := Array.push ◾ _x.9 _x.1;
      return _x.10
[Compiler.extractClosed] size: 3
    def Arr.dualArrayTable._closed_2 : Prod (Array Nat) (Array Nat) :=
      let _x.1 := Arr.dualArrayTable._closed_1;
      let _x.2 := Arr.dualArrayTable._closed_0;
      let _x.3 := Prod.mk ◾ ◾ _x.2 _x.1;
      return _x.3
[Compiler.extractClosed] size: 1
    def Arr.dualArrayTable : Prod (Array Nat) (Array Nat) :=
      let _x.1 := Arr.dualArrayTable._closed_2;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.extractClosed true in
def dualArrayTable : Array Nat × Array Nat := (#[1,2,3,4], #[4,5,6,7])

end Arr


namespace BArr

/--
trace: [Compiler.extractClosed] size: 19
    def BArr.arrayTable._closed_0 : ByteArray :=
      let _x.1 := 8;
      let _x.2 := 7;
      let _x.3 := 6;
      let _x.4 := 5;
      let _x.5 := 4;
      let _x.6 := 3;
      let _x.7 := 2;
      let _x.8 := 1;
      let _x.9 := 8;
      let _x.10 := Array.mkEmpty ◾ _x.9;
      let _x.11 := Array.push ◾ _x.10 _x.8;
      let _x.12 := Array.push ◾ _x.11 _x.7;
      let _x.13 := Array.push ◾ _x.12 _x.6;
      let _x.14 := Array.push ◾ _x.13 _x.5;
      let _x.15 := Array.push ◾ _x.14 _x.4;
      let _x.16 := Array.push ◾ _x.15 _x.3;
      let _x.17 := Array.push ◾ _x.16 _x.2;
      let _x.18 := Array.push ◾ _x.17 _x.1;
      let _x.19 := ByteArray.mk _x.18;
      return _x.19
[Compiler.extractClosed] size: 1
    def BArr.arrayTable : ByteArray :=
      let _x.1 := BArr.arrayTable._closed_0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.extractClosed true in
def arrayTable : ByteArray := ⟨#[1,2,3,4,5,6,7,8]⟩

@[noinline]
def myid (x : α) := x

/--
trace: [Compiler.extractClosed] size: 2
    def BArr.nonTrivialArrayTable._closed_0 : UInt8 :=
      let _x.1 := 2;
      let _x.2 := BArr.myid._redArg _x.1;
      return _x.2
[Compiler.extractClosed] size: 2
    def BArr.nonTrivialArrayTable._closed_1 : UInt8 :=
      let _x.1 := 5;
      let _x.2 := BArr.myid._redArg _x.1;
      return _x.2
[Compiler.extractClosed] size: 2
    def BArr.nonTrivialArrayTable._closed_2 : UInt8 :=
      let _x.1 := 7;
      let _x.2 := BArr.myid._redArg _x.1;
      return _x.2
[Compiler.extractClosed] size: 19
    def BArr.nonTrivialArrayTable._closed_3 : ByteArray :=
      let _x.1 := 8;
      let _x.2 := BArr.nonTrivialArrayTable._closed_2;
      let _x.3 := 6;
      let _x.4 := BArr.nonTrivialArrayTable._closed_1;
      let _x.5 := 4;
      let _x.6 := 3;
      let _x.7 := BArr.nonTrivialArrayTable._closed_0;
      let _x.8 := 1;
      let _x.9 := 8;
      let _x.10 := Array.mkEmpty ◾ _x.9;
      let _x.11 := Array.push ◾ _x.10 _x.8;
      let _x.12 := Array.push ◾ _x.11 _x.7;
      let _x.13 := Array.push ◾ _x.12 _x.6;
      let _x.14 := Array.push ◾ _x.13 _x.5;
      let _x.15 := Array.push ◾ _x.14 _x.4;
      let _x.16 := Array.push ◾ _x.15 _x.3;
      let _x.17 := Array.push ◾ _x.16 _x.2;
      let _x.18 := Array.push ◾ _x.17 _x.1;
      let _x.19 := ByteArray.mk _x.18;
      return _x.19
[Compiler.extractClosed] size: 1
    def BArr.nonTrivialArrayTable : ByteArray :=
      let _x.1 := BArr.nonTrivialArrayTable._closed_3;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.extractClosed true in
def nonTrivialArrayTable : ByteArray := ⟨#[1,myid 2,3,4,myid 5,6,myid 7,8]⟩

/--
trace: [Compiler.extractClosed] size: 11
    def BArr.dualArrayTable._closed_0 : ByteArray :=
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
[Compiler.extractClosed] size: 11
    def BArr.dualArrayTable._closed_1 : ByteArray :=
      let _x.1 := 7;
      let _x.2 := 6;
      let _x.3 := 5;
      let _x.4 := 4;
      let _x.5 := 4;
      let _x.6 := Array.mkEmpty ◾ _x.5;
      let _x.7 := Array.push ◾ _x.6 _x.4;
      let _x.8 := Array.push ◾ _x.7 _x.3;
      let _x.9 := Array.push ◾ _x.8 _x.2;
      let _x.10 := Array.push ◾ _x.9 _x.1;
      let _x.11 := ByteArray.mk _x.10;
      return _x.11
[Compiler.extractClosed] size: 3
    def BArr.dualArrayTable._closed_2 : Prod ByteArray ByteArray :=
      let _x.1 := BArr.dualArrayTable._closed_1;
      let _x.2 := BArr.dualArrayTable._closed_0;
      let _x.3 := Prod.mk ◾ ◾ _x.2 _x.1;
      return _x.3
[Compiler.extractClosed] size: 1
    def BArr.dualArrayTable : Prod ByteArray ByteArray :=
      let _x.1 := BArr.dualArrayTable._closed_2;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.extractClosed true in
def dualArrayTable : ByteArray × ByteArray := (⟨#[1,2,3,4]⟩, ⟨#[4,5,6,7]⟩)

end BArr


namespace FArr

/--
trace: [Compiler.extractClosed] size: 2
    def FArr.arrayTable._closed_0 : Float :=
      let _x.1 := 1;
      let _x.2 := Float.ofNat _x.1;
      return _x.2
[Compiler.extractClosed] size: 2
    def FArr.arrayTable._closed_1 : Float :=
      let _x.1 := 2;
      let _x.2 := Float.ofNat _x.1;
      return _x.2
[Compiler.extractClosed] size: 2
    def FArr.arrayTable._closed_2 : Float :=
      let _x.1 := 3;
      let _x.2 := Float.ofNat _x.1;
      return _x.2
[Compiler.extractClosed] size: 2
    def FArr.arrayTable._closed_3 : Float :=
      let _x.1 := 4;
      let _x.2 := Float.ofNat _x.1;
      return _x.2
[Compiler.extractClosed] size: 2
    def FArr.arrayTable._closed_4 : Float :=
      let _x.1 := 5;
      let _x.2 := Float.ofNat _x.1;
      return _x.2
[Compiler.extractClosed] size: 2
    def FArr.arrayTable._closed_5 : Float :=
      let _x.1 := 6;
      let _x.2 := Float.ofNat _x.1;
      return _x.2
[Compiler.extractClosed] size: 2
    def FArr.arrayTable._closed_6 : Float :=
      let _x.1 := 7;
      let _x.2 := Float.ofNat _x.1;
      return _x.2
[Compiler.extractClosed] size: 2
    def FArr.arrayTable._closed_7 : Float :=
      let _x.1 := 8;
      let _x.2 := Float.ofNat _x.1;
      return _x.2
[Compiler.extractClosed] size: 19
    def FArr.arrayTable._closed_8 : FloatArray :=
      let _x.1 := FArr.arrayTable._closed_7;
      let _x.2 := FArr.arrayTable._closed_6;
      let _x.3 := FArr.arrayTable._closed_5;
      let _x.4 := FArr.arrayTable._closed_4;
      let _x.5 := FArr.arrayTable._closed_3;
      let _x.6 := FArr.arrayTable._closed_2;
      let _x.7 := FArr.arrayTable._closed_1;
      let _x.8 := FArr.arrayTable._closed_0;
      let _x.9 := 8;
      let _x.10 := Array.mkEmpty ◾ _x.9;
      let _x.11 := Array.push ◾ _x.10 _x.8;
      let _x.12 := Array.push ◾ _x.11 _x.7;
      let _x.13 := Array.push ◾ _x.12 _x.6;
      let _x.14 := Array.push ◾ _x.13 _x.5;
      let _x.15 := Array.push ◾ _x.14 _x.4;
      let _x.16 := Array.push ◾ _x.15 _x.3;
      let _x.17 := Array.push ◾ _x.16 _x.2;
      let _x.18 := Array.push ◾ _x.17 _x.1;
      let _x.19 := FloatArray.mk _x.18;
      return _x.19
[Compiler.extractClosed] size: 1
    def FArr.arrayTable : FloatArray :=
      let _x.1 := FArr.arrayTable._closed_8;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.extractClosed true in
def arrayTable : FloatArray := ⟨#[1,2,3,4,5,6,7,8]⟩

@[noinline]
def myid (x : α) := x

/--
trace: [Compiler.extractClosed] size: 2
    def FArr.nonTrivialArrayTable._closed_0 : Float :=
      let _x.1 := FArr.arrayTable._closed_1;
      let _x.2 := FArr.myid._redArg _x.1;
      return _x.2
[Compiler.extractClosed] size: 2
    def FArr.nonTrivialArrayTable._closed_1 : Float :=
      let _x.1 := FArr.arrayTable._closed_4;
      let _x.2 := FArr.myid._redArg _x.1;
      return _x.2
[Compiler.extractClosed] size: 2
    def FArr.nonTrivialArrayTable._closed_2 : Float :=
      let _x.1 := FArr.arrayTable._closed_6;
      let _x.2 := FArr.myid._redArg _x.1;
      return _x.2
[Compiler.extractClosed] size: 19
    def FArr.nonTrivialArrayTable._closed_3 : FloatArray :=
      let _x.1 := FArr.arrayTable._closed_7;
      let _x.2 := FArr.nonTrivialArrayTable._closed_2;
      let _x.3 := FArr.arrayTable._closed_5;
      let _x.4 := FArr.nonTrivialArrayTable._closed_1;
      let _x.5 := FArr.arrayTable._closed_3;
      let _x.6 := FArr.arrayTable._closed_2;
      let _x.7 := FArr.nonTrivialArrayTable._closed_0;
      let _x.8 := FArr.arrayTable._closed_0;
      let _x.9 := 8;
      let _x.10 := Array.mkEmpty ◾ _x.9;
      let _x.11 := Array.push ◾ _x.10 _x.8;
      let _x.12 := Array.push ◾ _x.11 _x.7;
      let _x.13 := Array.push ◾ _x.12 _x.6;
      let _x.14 := Array.push ◾ _x.13 _x.5;
      let _x.15 := Array.push ◾ _x.14 _x.4;
      let _x.16 := Array.push ◾ _x.15 _x.3;
      let _x.17 := Array.push ◾ _x.16 _x.2;
      let _x.18 := Array.push ◾ _x.17 _x.1;
      let _x.19 := FloatArray.mk _x.18;
      return _x.19
[Compiler.extractClosed] size: 1
    def FArr.nonTrivialArrayTable : FloatArray :=
      let _x.1 := FArr.nonTrivialArrayTable._closed_3;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.extractClosed true in
def nonTrivialArrayTable : FloatArray := ⟨#[1,myid 2,3,4,myid 5,6,myid 7,8]⟩

/--
trace: [Compiler.extractClosed] size: 11
    def FArr.dualArrayTable._closed_0 : FloatArray :=
      let _x.1 := FArr.arrayTable._closed_3;
      let _x.2 := FArr.arrayTable._closed_2;
      let _x.3 := FArr.arrayTable._closed_1;
      let _x.4 := FArr.arrayTable._closed_0;
      let _x.5 := 4;
      let _x.6 := Array.mkEmpty ◾ _x.5;
      let _x.7 := Array.push ◾ _x.6 _x.4;
      let _x.8 := Array.push ◾ _x.7 _x.3;
      let _x.9 := Array.push ◾ _x.8 _x.2;
      let _x.10 := Array.push ◾ _x.9 _x.1;
      let _x.11 := FloatArray.mk _x.10;
      return _x.11
[Compiler.extractClosed] size: 11
    def FArr.dualArrayTable._closed_1 : FloatArray :=
      let _x.1 := FArr.arrayTable._closed_6;
      let _x.2 := FArr.arrayTable._closed_5;
      let _x.3 := FArr.arrayTable._closed_4;
      let _x.4 := FArr.arrayTable._closed_3;
      let _x.5 := 4;
      let _x.6 := Array.mkEmpty ◾ _x.5;
      let _x.7 := Array.push ◾ _x.6 _x.4;
      let _x.8 := Array.push ◾ _x.7 _x.3;
      let _x.9 := Array.push ◾ _x.8 _x.2;
      let _x.10 := Array.push ◾ _x.9 _x.1;
      let _x.11 := FloatArray.mk _x.10;
      return _x.11
[Compiler.extractClosed] size: 3
    def FArr.dualArrayTable._closed_2 : Prod FloatArray FloatArray :=
      let _x.1 := FArr.dualArrayTable._closed_1;
      let _x.2 := FArr.dualArrayTable._closed_0;
      let _x.3 := Prod.mk ◾ ◾ _x.2 _x.1;
      return _x.3
[Compiler.extractClosed] size: 1
    def FArr.dualArrayTable : Prod FloatArray FloatArray :=
      let _x.1 := FArr.dualArrayTable._closed_2;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.extractClosed true in
def dualArrayTable : FloatArray × FloatArray := (⟨#[1,2,3,4]⟩, ⟨#[4,5,6,7]⟩)

end FArr
