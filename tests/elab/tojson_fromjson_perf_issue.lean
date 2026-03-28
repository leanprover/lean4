import Lean.Data.Json
open Lean

structure Foo where
  a1 : Option Nat
  a2 : Option Nat
  a3 : Option Nat
  a4 : Option Nat
  a5 : Option Nat
  a6 : Option Nat
  a7 : Option Nat
  a8 : Option Nat
  a9 : Option Nat
  a10 : Option Nat
  a11 : Option Nat
  a12 : Option Nat
  a13 : Option Nat
  a14 : Option Nat
  a15 : Option Nat
  a16 : Option Nat
  a17 : Option Nat
  a18 : Option Nat
  a19 : Option Nat
  a20 : Option Nat
  a21 : Option Nat
  a22 : Option Nat
  a23 : Option Nat
  a24 : Option Nat
  a25 : Option Nat
  a26 : Option Nat
  a27 : Option Nat
  a28 : Option Nat
  a29 : Option Nat
  a30 : Option Nat
  a31 : Option Nat
  a32 : Option Nat
  a33 : Option Nat
  a34 : Option Nat
  a35 : Option Nat
  a36 : Option Nat
  a37 : Option Nat
  a38 : Option Nat
  a39 : Option Nat
  deriving ToJson, FromJson, Repr, BEq

structure Boo where
  a1 : String × Option Nat
  a2 : String × Option Nat
  a3 : String × Option Nat
  a4 : String × Option Nat
  a5 : String × Option Nat
  a6 : String × Option Nat
  a7 : String × Option Nat
  a8 : String × Option Nat
  a9 : String × Option Nat
  a10 : Array Nat
  a11 : Array Nat
  a12 : Array Nat
  a13 : Array Nat
  a14 : Array Nat
  a15 : Array Nat
  a16 : Array Nat
  a17 : Array Nat
  a18 : Array Nat
  a19 : Array Nat
  a20 : Array Nat
  a21 : Array Nat
  a22 : Array Nat
  a23 : Array Nat
  a24 : Array Nat
  a25 : Array Nat
  a26 : Array Nat
  a27 : Array Nat
  a28 : Array Nat
  a29 : List Nat
  a30 : List Nat
  a31 : List Nat
  a32 : List Nat
  a33 : List Nat
  a34 : List Nat
  a35 : List Nat
  a36 : List Nat
  a37 : List Nat
  a38 : List Nat
  a39 : List Nat
  aa10 : Float × USize × UInt64
  aa11 : Float × USize × UInt64
  aa12 : Float × USize × UInt64
  aa13 : Float × USize × UInt64
  aa14 : Float × USize × UInt64
  aa15 : Float × USize × UInt64
  aa16 : Float × USize × UInt64
  aa17 : Float × USize × UInt64
  aa18 : Float × USize × UInt64
  aa19 : Float × USize × UInt64
  aa20 : Float × USize × UInt64
  aa21 : Float × USize × UInt64
  aa22 : Float × USize × UInt64
  aa23 : Float × USize × UInt64
  aa24 : Float × USize × UInt64
  aa25 : Float × USize × UInt64
  aa26 : Float × USize × UInt64
  aa27 : Float × USize × UInt64
  aa28 : Float × USize × UInt64
  aa29 : Float × USize × UInt64
  aa30 : Float × USize × UInt64
  deriving ToJson, FromJson, Repr, BEq
