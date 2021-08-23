/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Gabriel Ebner, Marc Huisinga
-/
import Std.Data.RBTree
namespace Lean

-- mantissa * 10^-exponent
structure JsonNumber where
  mantissa : Int
  exponent : Nat
  deriving DecidableEq

namespace JsonNumber

protected def fromNat (n : Nat) : JsonNumber := ⟨n, 0⟩
protected def fromInt (n : Int) : JsonNumber := ⟨n, 0⟩

instance : Coe Nat JsonNumber := ⟨JsonNumber.fromNat⟩
instance : Coe Int JsonNumber := ⟨JsonNumber.fromInt⟩

private partial def countDigits (n : Nat) : Nat :=
  let rec loop (n digits : Nat) : Nat :=
    if n ≤ 9 then
      digits
    else
      loop (n/10) (digits+1)
  loop n 1

-- convert mantissa * 10^-exponent to 0.mantissa * 10^exponent
protected def normalize : JsonNumber → Int × Nat × Int
  | ⟨m, e⟩ => do
    if m = 0 then (0, 0, 0)
    else
      let sign : Int := if m > 0 then 1 else -1
      let mut mAbs := m.natAbs
      let nDigits := countDigits mAbs
      -- eliminate trailing zeros
      for _ in [0:nDigits] do
        if mAbs % 10 = 0 then
          mAbs := mAbs / 10
        else
          break
      (sign, mAbs, -(e : Int) + nDigits)

-- todo (Dany): We should have an Ordering version of this.
def lt (a b : JsonNumber) : Bool :=
  let (as, am, ae) := a.normalize
  let (bs, bm, be) := b.normalize
  match (as, bs) with
  | (-1, 1) => true
  | (1, -1) => false
  | _ =>
    let ((am, ae), (bm, be)) :=
      if as = -1 && bs = -1 then
        ((bm, be), (am, ae))
      else
        ((am, ae), (bm, be))
    let amDigits := countDigits am
    let bmDigits := countDigits bm
    -- align the mantissas
    let (am, bm) :=
      if amDigits < bmDigits then
        (am * 10^(bmDigits - amDigits), bm)
      else
        (am, bm * 10^(amDigits - bmDigits))
    if ae < be then true
    else if ae > be then false
    else am < bm

def ltProp : LT JsonNumber :=
  ⟨fun a b => lt a b = true⟩

instance : LT JsonNumber :=
  ltProp

instance (a b : JsonNumber) : Decidable (a < b) :=
  inferInstanceAs (Decidable (lt a b = true))

instance : Ord JsonNumber where
  compare x y :=
    if x < y then Ordering.lt
    else if x > y then Ordering.gt
    else Ordering.eq

protected def toString : JsonNumber → String
  | ⟨m, 0⟩ => m.repr
  | ⟨m, e⟩ =>
    let sign := if m ≥ 0 then "" else "-"
    let m := m.natAbs
    -- if there are too many zeroes after the decimal, we
    -- use exponents to compress the representation.
    -- this is mostly done for memory usage reasons:
    -- the size of the representation would otherwise
    -- grow exponentially in the value of exponent.
    let exp : Int := 9 + countDigits m - (e : Int)
    let exp := if exp < 0 then exp else 0
    let e' := (10 : Int) ^ (e - exp.natAbs)
    let left := (m / e').repr
    let right := e' + coe m % e'
      |>.repr.toSubstring.drop 1
      |>.dropRightWhile (fun c => c = '0')
      |>.toString
    let exp := if exp = 0 then "" else "e" ++ exp.repr
    s!"{sign}{left}.{right}{exp}"

-- shift a JsonNumber by a specified amount of places to the left
protected def shiftl : JsonNumber → Nat → JsonNumber
  -- if s ≤ e, then 10 ^ (s - e) = 1, and hence the mantissa remains unchanged.
  -- otherwise, the expression pads the mantissa with zeroes
  -- to accomodate for the remaining places to shift.
  | ⟨m, e⟩, s => ⟨m * (10 ^ (s - e) : Nat), e - s⟩

-- shift a JsonNumber by a specified amount of places to the right
protected def shiftr : JsonNumber → Nat → JsonNumber
  | ⟨m, e⟩, s => ⟨m, e + s⟩

instance : ToString JsonNumber := ⟨JsonNumber.toString⟩

instance : Repr JsonNumber where
  reprPrec | ⟨m, e⟩, _ => Std.Format.bracket "⟨" (repr m ++ "," ++ repr e) "⟩"

end JsonNumber

def strLt (a b : String) := Decidable.decide (a < b)

open Std (RBNode RBNode.leaf)

inductive Json where
  | null
  | bool (b : Bool)
  | num (n : JsonNumber)
  | str (s : String)
  | arr (elems : Array Json)
  -- uses RBNode instead of RBMap because RBMap is a def
  -- and thus currently cannot be used to define a type that
  -- is recursive in one of its parameters
  | obj (kvPairs : RBNode String (fun _ => Json))
  deriving Inhabited

namespace Json

private partial def beq' : Json → Json → Bool
  | null,   null   => true
  | bool a, bool b => a == b
  | num a,  num b  => a == b
  | str a,  str b  => a == b
  | arr a,  arr b  =>
    let _ : BEq Json := ⟨beq'⟩
    a == b
  | obj a,  obj b =>
    let _ : BEq Json := ⟨beq'⟩
    let szA := a.fold (init := 0) (fun a _ _ => a + 1)
    let szB := b.fold (init := 0) (fun a _ _ => a + 1)
    szA == szB && a.all fun field fa =>
      match b.find compare field with
      | none    => false
      | some fb => fa == fb
  | _,      _      => false

instance : BEq Json where
  beq := beq'

-- HACK(Marc): temporary ugliness until we can use RBMap for JSON objects
def mkObj (o : List (String × Json)) : Json :=
  obj $ do
    let mut kvPairs := RBNode.leaf
    for ⟨k, v⟩ in o do
      kvPairs := kvPairs.insert compare k v
    kvPairs

instance : Coe Nat Json := ⟨fun n => Json.num n⟩
instance : Coe Int Json := ⟨fun n => Json.num n⟩
instance : Coe String Json := ⟨Json.str⟩
instance : Coe Bool Json := ⟨Json.bool⟩

def isNull : Json -> Bool
  | null => true
  | _    => false

def getObj? : Json → Except String (RBNode String (fun _ => Json))
  | obj kvs => kvs
  | _       => throw "object expected"

def getArr? : Json → Except String (Array Json)
  | arr a => a
  | _     => throw "array expected"

def getStr? : Json → Except String String
  | str s => s
  | _     => throw "String expected"

def getNat? : Json → Except String Nat
  | (n : Nat) => n
  | _         => throw "Natural number expected"

def getInt? : Json → Except String Int
  | (i : Int) => i
  | _         => throw "Integer expected"

def getBool? : Json → Except String Bool
  | (b : Bool) => b
  | _          => throw "Bool expected"

def getNum? : Json → Except String JsonNumber
  | num n => n
  | _     => throw "number expected"

def getObjVal? : Json → String → Except String Json
  | obj kvs, k =>
    match kvs.find compare k with
    | some v => v
    | none => throw s!"property not found: {k}"
  | _      , _ => throw "object expected"

def getArrVal? : Json → Nat → Except String Json
  | arr a, i =>
    match a.get? i with
    | some v => v
    | none => throw s!"index out of bounds: {i}"
  | _    , _ => throw "array expected"

def getObjValD (j : Json) (k : String) : Json :=
  (j.getObjVal? k).toOption.getD null

def setObjVal! : Json → String → Json → Json
  | obj kvs, k, v => obj <| kvs.insert compare k v
  | j      , _, _ => panic! "Json.setObjVal!: not an object: {j}"

inductive Structured where
  | arr (elems : Array Json)
  | obj (kvPairs : RBNode String (fun _ => Json))

instance : Coe (Array Json) Structured := ⟨Structured.arr⟩
instance : Coe (RBNode String (fun _ => Json)) Structured := ⟨Structured.obj⟩

end Json
end Lean
