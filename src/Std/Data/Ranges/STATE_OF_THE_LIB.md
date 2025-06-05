# Just a place for some working notes about the iterators/ranges/slices

## Ranges with step sizes

*At least* in the `Nat` case, the finiteness of a range `a,,b` only depends on the type of its bounds -- but only as long as range doesn't have a custom step size.

* If the step size is positive, we are still able to determine the termination behavior based on the bound types. (`1,,→2→,,5`)
* If the step size is zero, the range is either empty or infinite. (`1,,→0→,,5`)

For many operations, we need to know the termination behavior:

* `(1,,→2→,,5).iter.toList`
* `for x in ((1 : Nat),,→2→,,5) do`

Both of these cases fail because they rely on the inference of `Finite` and `ForIn` instances.

The `toList` example can be made to work by making `toList` take a proof of finiteness, which is implicitly inferred using a `get_elem_tactic`-like extensible tactic (see `Std.Data.Iterators.Combinators.Monadic.Lineage` for a rough draft).

However, `for ... in` notation essentially relies on the synthesis of a `ForIn` instance and we cannot use `iterator_finite_tactic` for this.

The best (and still bad) idea I can come up with is to overload the range notation, and to make the higher-prioritized implementation try to annotate the range with a finiteness hint. If that fails, the lower-prioritized implementation kicks in and `for ... in` etc. will not work without tricks (`allowNontermination` or supplying a proof manually).

