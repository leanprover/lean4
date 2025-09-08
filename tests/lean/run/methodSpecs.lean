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

-- Now some error conditions

/-- error: `Foo` is not a definition -/
#guard_msgs in @[method_specs] inductive Foo

/--
error: expected `foo` to be a type class instance, but its's type `Nat` does not look like a class.
-/
#guard_msgs in @[method_specs] def foo := 1

structure S where field : Nat
/--
error: expected `aS` to be a type class instance, but its's type `S` does not look like a class.
-/
#guard_msgs in @[method_specs] def aS : S := ⟨1⟩

@[class] inductive indClass where | mk
/-- error: `indClass` is not a structure -/
#guard_msgs in @[method_specs] def instIndClass : indClass := .mk

-- This used to fail until we eta-reduced the field values
@[method_specs] instance anotherInstBEqL [BEq α] : BEq (L α) := ⟨fun x y => L.beqImpl x y⟩

def L.badBeqImpl : L α → L α → Bool
  | nil, nil           => true
  | cons _ xs, cons _ ys => L.badBeqImpl xs ys
  | _, _               => false

/-- error: function `@L.badBeqImpl` does not take its arguments in the same order as the instance -/
#guard_msgs in
@[method_specs] instance badInstBEqL [BEq α] : BEq (L α) := ⟨L.badBeqImpl⟩
