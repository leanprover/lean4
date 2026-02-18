Transparency Settings and v4.29 Migration Guide
================================================

This document explains the transparency system in Lean's definitional equality checker (`isDefEq`)
and the changes introduced in v4.29. It is aimed at both users migrating their code and developers
working on the Lean implementation.

Background
----------

### "Try-hard" vs "speculative" isDefEq

The definitional equality checker (`isDefEq`) operates in two very different contexts:

1. **Type checking user input.** We assume the user's input is most likely correct. We want Lean to
   try hard before reporting a failure. In this context, it is fine to unfold `[semireducible]`
   definitions (the `TransparencyMode.default` setting).

2. **Proof automation** (`simp`, `rw`, type class resolution). We perform many speculative `isDefEq`
   calls — most of which *fail*. In this context, we do *not* want to try hard. Unfolding too
   many definitions is a performance footgun. This is why `TransparencyMode.reducible` exists.

### The transparency hierarchy

Lean has four reducibility statuses (`ReducibilityStatus`) and five transparency modes
(`TransparencyMode`). The transparency modes form a linear order:

    none < reducible < instances < default < all

Each level unfolds everything the previous level does, plus more.

| TransparencyMode | Unfolds                                    | Typical use                               |
|------------------|--------------------------------------------|-------------------------------------------|
| `reducible`      | `[reducible]` definitions                  | Speculative `isDefEq` in proof automation |
| `instances`      | Also `[instance_reducible]` definitions    | Instance-implicit argument checking       |
| `default`        | Also `[semireducible]` (anything not `[irreducible]`) | Type checking user input       |
| `all`            | Also `[irreducible]` definitions           | Rarely used                               |

**`[reducible]`** definitions are eagerly unfolded when indexing terms into discrimination trees
(used by `simp` and type class resolution) and in `grind`. They still appear in user-facing terms
outside of indexing. Think of `[reducible]` as `[inline]` for indexing.

**`[instance_reducible]`** is the transparency used for type class instances. Instances cannot be
eagerly reduced — they expand into large terms. But they must be unfoldable during `isDefEq` to
resolve instance diamonds. For example, `Add Nat` can come from a direct instance or via
`Semiring`. These different instances are definitionally equal but structurally different, so
`isDefEq` must unfold them to confirm equality. Discrimination trees do not index instances, so
unfolding at `.instances` during speculative checks does not cause the same performance issues as
`.default`.

### Why implicit arguments matter

When `simp` or `rw` applies a lemma, explicit arguments are matched at the caller's transparency
(typically `.reducible`). But implicit arguments are "invisible" to the user — they don't choose
them directly. If a lemma fails to apply because an implicit argument doesn't match at `.reducible`,
the user sees a confusing failure with no obvious cause. Consider applying `List.append_assoc`:

```
∀ (as bs cs : List α), as ++ bs ++ cs = as ++ (bs ++ cs)
```

The explicit arguments `as`, `bs`, `cs` are straightforward to match. But the type `α` is implicit
and must be inferred. If the types involve semireducible definitions, the match might fail at
`.reducible` even though the types are definitionally equal at `.default`.

Changes in v4.29
-----------------

### Decoupling instances from transparency (`instance_reducible`)

Previously, the `instance` command coupled two orthogonal concerns: registering a definition for
type class resolution and setting its transparency. In v4.29, these are decoupled:

- `[instance]` registers a definition for type class resolution.
- `[instance_reducible]` sets its transparency to be unfolded at `.instances` or above.

The `instance` command adds both attributes automatically. The decoupling is important because
whether a definition is available for type class resolution should not affect its transparency.
Instances may be scoped or local — they may be available for resolution in one context but not
another. Users may also manually construct instances using their own definitions:

```lean
def myAdd : Add Nat := ⟨Nat.add⟩
```

If `myAdd` is later registered as an instance (even locally or in a scoped namespace), its
transparency must already be `[instance_reducible]` so that `isDefEq` can unfold it when
resolving instance diamonds. The transparency is a property of the definition itself, not of
whether it happens to be registered for resolution in the current scope.

Lean generates a warning if `[instance]` is used on a definition that is neither
`[instance_reducible]` nor `[reducible]`. When using `attribute [instance]` on an existing
definition, you typically also need `attribute [instance_reducible]`:

```lean
attribute [instance_reducible, instance] myAdd
```

### Respecting transparency for implicit arguments (`backward.isDefEq.respectTransparency`)

**Old behavior:** When processing implicit arguments during proof automation, Lean bumped
transparency to `.default`, unfolding all semireducible definitions. This ensured that implicit
arguments would "just work" from the user's perspective.

**Problem:** This meant that every speculative `isDefEq` call in proof automation could trigger
expensive unfolding on implicit arguments — and most of these calls *fail*. This eventually became
a performance bottleneck in Mathlib.

**New behavior (default in v4.29):** Implicit arguments are checked at the caller's transparency,
except instance-implicit arguments (`[..]`) which are checked at `TransparencyMode.instances`.
The option `backward.isDefEq.respectTransparency` controls this behavior (`true` = new, `false` =
old).

### Reducible class fields (`backward.whnf.reducibleClassField`)

Some type class fields are marked `[reducible]` because they define type aliases. For example,
`MonadControlT.stM : Type u → Type u` is `[reducible]` so that `stM m (ExceptT ε m) α` reduces
to `Except ε α`. However, simply unfolding the class field gives an expression like
`instMonadControlTOfMonadControl.1 α`, which is stuck at `.reducible` because the instance
`instMonadControlTOfMonadControl` is `[instance_reducible]`, not `[reducible]`.

When `backward.whnf.reducibleClassField` is `true`, unfolding a `[reducible]` class field at
`.reducible` also unfolds the associated instance projection at `.instances`, so the reduction
completes as the user expects.

Migration Guide
---------------

### Common patterns

**1. Adding `[instance_reducible]` to `attribute [instance]`**

If you have:
```lean
attribute [instance] MyClass.field
```
You likely need:
```lean
attribute [instance_reducible, instance] MyClass.field
```

This is the most common change needed. Any definition that is used as an instance needs
`[instance_reducible]` so that `isDefEq` can unfold it when resolving instance diamonds.

**2. Arithmetic and structural equalities**

Definitions like `Nat.add`, `Nat.mul`, `Array.size`, `List.length` are `[semireducible]`. Under the
old behavior, they were unfolded when checking implicit arguments. Now they are not. You may see
failures like:

```
w * (curr + 1) =?= w * curr + w
```

**Workarounds:**
- Add appropriate `simp` lemmas or `unif_hint` declarations.
- Mark definitions as `[reducible]` if they should truly be transparent everywhere (e.g.,
  `Array.size` may be a candidate since `Array.size xs = xs.toList.length` by definition).

**3. Using `simp` lemmas for class field reductions**

When a `[reducible]` class field doesn't reduce because the instance is only
`[instance_reducible]`, you can add a `simp` lemma:

```lean
@[simp] theorem ExceptT.stM [Monad m] : stM m (ExceptT ε m) α = Except ε α := rfl
```

### Debugging technique

When a proof breaks, use this approach to identify missing annotations:

1. Add `set_option backward.isDefEq.respectTransparency false` to confirm the old behavior works.
2. Add `set_option diagnostics true` and `set_option diagnostics.threshold 0`.
3. Compare the unfolded declarations with and without `backward.isDefEq.respectTransparency`.
4. The declarations that appear only in the `false` trace are the ones that need annotation changes
   (typically `[instance_reducible]`).

For type class synthesis failures specifically:

1. Add `set_option trace.Meta.synthInstance true` and
   `set_option backward.isDefEq.respectTransparency false`.
2. Save the successful synthesis path.
3. Remove the `set_option`, find the first failure, and add the missing `[instance_reducible]`
   annotation.
4. Repeat.

### Backward compatibility options

| Option | Default | Effect |
|--------|---------|--------|
| `backward.isDefEq.respectTransparency` | `true` | When `false`, bumps to `.default` for implicit args (old behavior) |
| `backward.whnf.reducibleClassField` | `false` | When `true`, unfolds instance projections when reducing `[reducible]` class fields |

These are intended as migration aids. We expect both to stabilize (the first staying `true`, the
second likely becoming `true` by default) as the ecosystem adapts.
