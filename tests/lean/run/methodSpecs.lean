inductive L α where
  | nil  : L α
  | cons : α → L α → L α

def L.beqImpl [BEq α] : L α → L α → Bool
  | nil, nil           => true
  | cons x xs, cons y ys => x == y && L.beqImpl xs ys
  | _, _               => false

@[method_specs] instance [BEq α] : BEq (L α) := ⟨L.beqImpl⟩

/--
info: theorem instBEqL.beq_spec.{u_1} : ∀ {α : Type u_1} [inst : BEq α] (x x_1 : L α),
  (x == x_1) =
    match x, x_1 with
    | L.nil, L.nil => true
    | L.cons x xs, L.cons y ys => x == y && xs == ys
    | x, x_2 => false
-/
#guard_msgs(pass trace, all) in
#print sig instBEqL.beq_spec

/--
info: theorem instBEqL.beq_spec_1.{u_1} : ∀ {α : Type u_1} [inst : BEq α], (L.nil == L.nil) = true
-/
#guard_msgs(pass trace, all) in
#print sig instBEqL.beq_spec_1

/--
info: theorem instBEqL.beq_spec_2.{u_1} : ∀ {α : Type u_1} [inst : BEq α] (x_2 : α) (xs : L α) (y : α) (ys : L α),
  (L.cons x_2 xs == L.cons y ys) = (x_2 == y && xs == ys)
-/
#guard_msgs(pass trace, all) in
#print sig instBEqL.beq_spec_2

/--
info: theorem instBEqL.beq_spec_3.{u_1} : ∀ {α : Type u_1} [inst : BEq α] (x x_1 : L α),
  (x = L.nil → x_1 = L.nil → False) →
    (∀ (x_2 : α) (xs : L α) (y : α) (ys : L α), x = L.cons x_2 xs → x_1 = L.cons y ys → False) → (x == x_1) = false
-/
#guard_msgs(pass trace, all) in
#print sig instBEqL.beq_spec_3

/-- error: Unknown constant `instBEqL.beq_spec_4` -/
#guard_msgs(pass trace, all) in
#print sig instBEqL.beq_spec_4

-- Other names are not reserved

/-- error: Unknown constant `instBEqL.eq_spec` -/
#guard_msgs in #print sig instBEqL.eq_spec

/-- error: Unknown constant `instBEqL.beq_spec_` -/
#guard_msgs in #print sig instBEqL.beq_spec_

-- Test rewriting all the way to HAppend. This tests `@[method_specs_simp]`, and that
-- `Init` has that set up properly

def L.append {α : Type u} : L α → L α → L α
  | nil, ys       => ys
  | cons x xs, ys => cons x (L.append xs ys)

@[method_specs] instance (α : Type u) : Append (L α) where
  append := L.append

/--
info: theorem instAppendL.append_spec_2.{u} : ∀ {α : Type u} (x : L α) (x_2 : α) (xs : L α),
  L.cons x_2 xs ++ x = L.cons x_2 (xs ++ x)
-/
#guard_msgs in #print sig instAppendL.append_spec_2

-- Test that rewriting works with non-rfl theorem too

class Cls α where op : α → α
class HCls α where hOp : α → α
instance instHClsOfCls [Cls α] : HCls α where hOp := Cls.op
-- NB: Not a rfl theorem
@[method_specs_simp] theorem Cls.op_eq_hOp : @Cls.op α inst = @HCls.hOp α (@instHClsOfCls α inst) := (rfl)

def L.op {α : Type u} : L α → L α
  | nil        => nil
  | cons x xs  => cons x (L.op xs)
@[method_specs] instance : Cls (L α) where op := L.op

/--
info: theorem instClsL.op_spec_2.{u} : ∀ {α : Type u} (x_1 : α) (xs : L α),
  HCls.hOp (L.cons x_1 xs) = L.cons x_1 (HCls.hOp xs)
-/
#guard_msgs in
#print sig instClsL.op_spec_2


/-!
Now some error conditions
-/

/-- error: `Foo` is not a definition -/
#guard_msgs in @[method_specs] inductive Foo

/--
error: expected `foo` to be a type class instance, but its type `Nat` does not look like a class.
-/
#guard_msgs in @[method_specs] def foo := 1

structure S where field : Nat
/--
error: expected `aS` to be a type class instance, but its type `S` does not look like a class.
-/
#guard_msgs in @[method_specs] def aS : S := ⟨1⟩

@[class] inductive indClass where | mk
/-- error: `indClass` is not a structure -/
#guard_msgs in @[method_specs] def instIndClass : indClass := .mk

-- This used to fail until we eta-reduced the field values
@[method_specs] instance anotherInstBEqL [BEq α] : BEq (L α) := ⟨fun x y => L.beqImpl x y⟩

def L.badBeqImpl {α : Type u} : L α → L α → Bool
  | nil, nil           => true
  | cons _ xs, cons _ ys => L.badBeqImpl xs ys
  | _, _               => false

/-- error: function `@L.badBeqImpl` does not take its arguments in the same order as the instance -/
#guard_msgs in
@[method_specs] instance badInstBEqL [BEq α] : BEq (L α) := ⟨L.badBeqImpl⟩

-- L.append has a more general type (in terms of universes)
-- than the instance below.
-- This should be caught and warned about.

def L.badAppend : L α → L α → L α
  | nil, ys       => ys
  | cons x xs, ys => cons x (L.badAppend xs ys)

/--
error: function `@L.badAppend` is called with universe parameters
  [u+1]
which differs from the instances' universe parameters
  [u]
-/
#guard_msgs in
@[method_specs] instance badInstAppendL (α : Type u) : Append (L α) where
  append := L.badAppend
