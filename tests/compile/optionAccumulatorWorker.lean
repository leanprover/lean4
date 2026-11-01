module

/-!
An `Option` accumulator passed through a tail-recursive list loop should be
carried as its payload inside the loop. Check the generated workers for both
scalar and heap-allocated payloads, as well as a loop that cannot use a worker.
Also check that a user declaration with the generated worker name is preserved.
-/

public section

set_option compiler.check true

/--
trace: [Compiler.saveMono] size: 5
    def lastUInt8._optionAccumulatorWorker x.1 payload : Option UInt8 :=
      cases x.1 : Option UInt8
      | List.nil =>
        let finalSome := some ◾ payload;
        return finalSome
      | List.cons head.2 tail.3 =>
        let recResult := lastUInt8._optionAccumulatorWorker tail.3 head.2;
        return recResult
[Compiler.saveMono] size: 4
    def lastUInt8 x.1 x.2 : Option UInt8 :=
      cases x.1 : Option UInt8
      | List.nil =>
        return x.2
      | List.cons head.3 tail.4 =>
        let result := lastUInt8._optionAccumulatorWorker tail.4 head.3;
        return result
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
def lastUInt8 : List UInt8 → Option UInt8 → Option UInt8
  | [], last => last
  | x :: xs, _ => lastUInt8 xs (some x)

def lastUInt64 : List UInt64 → Option UInt64 → Option UInt64
  | [], last => last
  | x :: xs, _ => lastUInt64 xs (some x)

def lastUInt16 : List UInt16 → Option UInt16 → Option UInt16
  | [], last => last
  | x :: xs, _ => lastUInt16 xs (some x)

def lastUInt32 : List UInt32 → Option UInt32 → Option UInt32
  | [], last => last
  | x :: xs, _ => lastUInt32 xs (some x)

def lastUSize : List USize → Option USize → Option USize
  | [], last => last
  | x :: xs, _ => lastUSize xs (some x)

def lastChar : List Char → Option Char → Option Char
  | [], last => last
  | x :: xs, _ => lastChar xs (some x)

/--
trace: [Compiler.saveMono] size: 5
    def lastFloat._optionAccumulatorWorker x.1 payload : Option Float :=
      cases x.1 : Option Float
      | List.nil =>
        let finalSome := some ◾ payload;
        return finalSome
      | List.cons head.2 tail.3 =>
        let recResult := lastFloat._optionAccumulatorWorker tail.3 head.2;
        return recResult
[Compiler.saveMono] size: 4
    def lastFloat x.1 x.2 : Option Float :=
      cases x.1 : Option Float
      | List.nil =>
        return x.2
      | List.cons head.3 tail.4 =>
        let result := lastFloat._optionAccumulatorWorker tail.4 head.3;
        return result
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
def lastFloat : List Float → Option Float → Option Float
  | [], last => last
  | x :: xs, _ => lastFloat xs (some x)

def lastFloat32 : List Float32 → Option Float32 → Option Float32
  | [], last => last
  | x :: xs, _ => lastFloat32 xs (some x)

/--
trace: [Compiler.saveMono] size: 5
    def lastString._optionAccumulatorWorker x.1 payload : Option String :=
      cases x.1 : Option String
      | List.nil =>
        let finalSome := some ◾ payload;
        return finalSome
      | List.cons head.2 tail.3 =>
        let recResult := lastString._optionAccumulatorWorker tail.3 head.2;
        return recResult
[Compiler.saveMono] size: 4
    def lastString x.1 x.2 : Option String :=
      cases x.1 : Option String
      | List.nil =>
        return x.2
      | List.cons head.3 tail.4 =>
        let result := lastString._optionAccumulatorWorker tail.4 head.3;
        return result
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
def lastString : List String → Option String → Option String
  | [], last => last
  | x :: xs, _ => lastString xs (some x)

/--
trace: [Compiler.saveMono] size: 5
    def lastUInt8Reset x.1 x.2 : Option UInt8 :=
      cases x.1 : Option UInt8
      | List.nil =>
        return x.2
      | List.cons head.3 tail.4 =>
        let _x.5 := none ◾;
        let _x.6 := lastUInt8Reset tail.4 _x.5;
        return _x.6
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
def lastUInt8Reset : List UInt8 → Option UInt8 → Option UInt8
  | [], last => last
  | _ :: xs, _ => lastUInt8Reset xs none

namespace lastUInt8Collision

def _optionAccumulatorWorker : Nat := 23

end lastUInt8Collision

def lastUInt8Collision : List UInt8 → Option UInt8 → Option UInt8
  | [], last => last
  | x :: xs, _ => lastUInt8Collision xs (some x)

def lastNat : List Nat → Option Nat → Option Nat
  | [], last => last
  | x :: xs, _ => lastNat xs (some x)

structure Payload where
  value : Nat
  deriving BEq

def lastPayload : List Payload → Option Payload → Option Payload
  | [], last => last
  | x :: xs, _ => lastPayload xs (some x)

def main : IO Unit := do
  for n in [0:300] do
    let xs8 := (List.range n).map UInt8.ofNat
    let xs16 := (List.range n).map UInt16.ofNat
    let xs32 := (List.range n).map UInt32.ofNat
    let xs64 := (List.range n).map UInt64.ofNat
    let xsUSize := (List.range n).map USize.ofNat
    let xsChar := List.replicate n 'λ'
    let xsFloat := List.replicate n (1.25 : Float)
    let xsFloat32 := List.replicate n (1.25 : Float32)
    let xsString := (List.range n).map toString
    let xsNat := List.range n
    let xsPayload := (List.range n).map (Payload.mk ·)
    for initial in #[none, some (0 : UInt8), some (255 : UInt8)] do
      let expected := xs8.getLast?.orElse fun _ => initial
      unless lastUInt8 xs8 initial == expected do
        throw <| IO.userError s!"UInt8 mismatch at length {n}"
    for initial in #[none, some (0 : UInt64), some (18446744073709551615 : UInt64)] do
      let expected := xs64.getLast?.orElse fun _ => initial
      unless lastUInt64 xs64 initial == expected do
        throw <| IO.userError s!"UInt64 mismatch at length {n}"
    for initial in #[none, some (0 : UInt16), some (65535 : UInt16)] do
      let expected := xs16.getLast?.orElse fun _ => initial
      unless lastUInt16 xs16 initial == expected do
        throw <| IO.userError s!"UInt16 mismatch at length {n}"
    for initial in #[none, some (0 : UInt32), some (4294967295 : UInt32)] do
      let expected := xs32.getLast?.orElse fun _ => initial
      unless lastUInt32 xs32 initial == expected do
        throw <| IO.userError s!"UInt32 mismatch at length {n}"
    for initial in #[none, some (0 : USize), some (23 : USize)] do
      let expected := xsUSize.getLast?.orElse fun _ => initial
      unless lastUSize xsUSize initial == expected do
        throw <| IO.userError s!"USize mismatch at length {n}"
    for initial in #[none, some ('a' : Char), some ('🙂' : Char)] do
      let expected := xsChar.getLast?.orElse fun _ => initial
      unless lastChar xsChar initial == expected do
        throw <| IO.userError s!"Char mismatch at length {n}"
    for initial in #[none, some (0.5 : Float), some (2.5 : Float)] do
      let expected := xsFloat.getLast?.orElse fun _ => initial
      unless lastFloat xsFloat initial == expected do
        throw <| IO.userError s!"Float mismatch at length {n}"
    for initial in #[none, some (0.5 : Float32), some (2.5 : Float32)] do
      let expected := xsFloat32.getLast?.orElse fun _ => initial
      unless lastFloat32 xsFloat32 initial == expected do
        throw <| IO.userError s!"Float32 mismatch at length {n}"
    for initial in #[none, some "", some "hello, λ"] do
      let expected := xsString.getLast?.orElse fun _ => initial
      unless lastString xsString initial == expected do
        throw <| IO.userError s!"String mismatch at length {n}"
    unless lastUInt8Reset xs8 (some 5) == (if xs8.isEmpty then some 5 else none) do
      throw <| IO.userError s!"reset mismatch at length {n}"
    unless lastUInt8Collision._optionAccumulatorWorker == 23 &&
        lastUInt8Collision xs8 none == xs8.getLast? do
      throw <| IO.userError s!"name collision mismatch at length {n}"
    for initial in #[none, some (0 : Nat), some (100000000000000000000 : Nat)] do
      let expected := xsNat.getLast?.orElse fun _ => initial
      unless lastNat xsNat initial == expected do
        throw <| IO.userError s!"Nat mismatch at length {n}"
    for initial in #[none, some (Payload.mk 0), some (Payload.mk 123)] do
      let expected := xsPayload.getLast?.orElse fun _ => initial
      unless lastPayload xsPayload initial == expected do
        throw <| IO.userError s!"Payload mismatch at length {n}"
  IO.println "option accumulator worker: ok"
