/-!
# `mutual_multiuniverse`: blocks the lowering must refuse

Each block below must produce an error rather than a silently wrong
translation, so the messages are pinned.
-/

/-! ## A nested occurrence of a block member

`List N2` is not a field the shadow can reconstruct: the shadow's `N2` carries
no data, so there is nothing to squash a `List N2` into elementwise without
lowering `List` itself. -/

/--
error: Unsupported constructor field in `mutual_multiuniverse` block: field 1 of `N1.mk` mentions a member of the block in a nested position, in the type
  List N2

Note: Nested occurrences are not supported: the shadow of a data member carries no data, so there is nothing to rebuild such a field from without lowering the surrounding type as well
-/
#guard_msgs in
mutual_multiuniverse
inductive N1 : Prop where
  | mk : List N2 → N1
inductive N2 : Type where
  | mk : N1 → N2
end

/-! ## A member occurring in the *domain* of a field

`(N4 → Nat) → N3` is not strictly positive; `mutual` rejects it too, but the
lowering has to say so before the kernel gets a chance. -/

/--
error: Unsupported constructor field in `mutual_multiuniverse` block: field 1 of `N3.mk` takes an argument whose type mentions a member of the block

Note: This is not a strictly positive occurrence, so the lowering has nothing to translate it to
-/
#guard_msgs in
mutual_multiuniverse
inductive N3 : Prop where
  | mk : (N4 → Nat) → N3
inductive N4 : Type where
  | mk : N3 → N4
end

/-! ## Only `inductive` declarations are allowed -/

/--
error: invalid `mutual_multiuniverse` block: every element of the block must be an `inductive` declaration
-/
#guard_msgs in
mutual_multiuniverse
inductive S1 : Prop where
  | mk : S2 → S1
structure S2 : Type 1 where
  fld : Type
end

/-! ## A field that does not fit its own member's universe is still an error;
the check is just made per member rather than for the block as a whole. -/

/--
error: Invalid universe level in constructor `U2.mk`: Parameter `t` has type
  Type 1
at universe level
  3
which is not less than or equal to the inductive type's resulting universe level
  1
-/
#guard_msgs in
mutual_multiuniverse
inductive U1 : Prop where
  | mk : U2 → U1
inductive U2 : Type 0 where
  | mk : (t : Type 1) → U1 → U2
end

/-! ## A large-eliminating `Prop` is reported the way `mutual` reports it

`mutualRec` is computable wherever the block has data to compute with.  A
block that is all `Prop` has none, so a large-eliminating member's `mutualRec`
is `noncomputable`, exactly as that member's own `rec` is -- and says so
rather than failing inside the code generator. -/

mutual_multiuniverse
inductive Sq : Prop where
  | mk : Sq
end

/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Sq.mutualRec', which is 'noncomputable'
-/
#guard_msgs in
def sqNat : Sq → Nat := fun s => Sq.mutualRec (motive := fun _ => Nat) 5 s

/-! ## A member whose `Prop`-ness depends on a universe parameter

Whether a member is `Prop` decides whether it becomes a shadow or an honest
inductive, so it has to be decidable from the declaration.  A member at `Sort u`
or `Sort (imax u v)` is `Prop` for some instantiations and not for others, and
is refused upstream before the lowering runs.  Contrast a *field* at
`Sort (imax _ _)`, which is fine -- see `mutualMultiuniverseFeatures`. -/

universe u v

/--
error: Invalid universe polymorphic resulting type: The resulting universe is not `Prop`, but it may be `Prop` for some parameter values:
  Sort u

Hint: A possible solution is to use levels of the form `max 1 _` or `_ + 1` to ensure the universe is of the form `Type _`
-/
#guard_msgs in
mutual_multiuniverse
inductive EA : Prop where
  | mk : EB → EA
inductive EB : Sort u where
  | leaf : Nat → EB
  | fromA : EA → EB
end

/--
error: Invalid universe polymorphic resulting type: The resulting universe is not `Prop`, but it may be `Prop` for some parameter values:
  Sort (imax u v)

Hint: A possible solution is to use levels of the form `max 1 _` or `_ + 1` to ensure the universe is of the form `Type _`
-/
#guard_msgs in
mutual_multiuniverse
inductive FA (α : Type u) (P : α → Sort v) : Prop where
  | mk : FB α P → FA α P
inductive FB (α : Type u) (P : α → Sort v) : Sort (imax u v) where
  | fn : ((a : α) → P a) → FB α P
  | back : FA α P → FB α P
end

/-! ## Two data members of one component at different universes

They hold each other, so each universe would have to be at most the other; only
the first direction gets as far as being reported. -/

/--
error: Invalid universe level in constructor `GB.toC`: Parameter has type
  GC
at universe level
  v + 1
which is not less than or equal to the inductive type's resulting universe level
  u + 1
-/
#guard_msgs in
mutual_multiuniverse
inductive GA : Prop where
  | mk : GB → GA
inductive GB : Type u where
  | leaf : Nat → GB
  | toC : GC → GB
inductive GC : Type v where
  | fromB : GB → GC
end
