algebra
=======

Algebraic structures.

* [priority](priority.lean) : priority for algebraic operations
* [relation](relation.lean)
* [binary](binary.lean) : binary operations
* [order](order.lean)
* [lattice](lattice.lean)
* [complete lattice](complete_lattice.lean)
* [group](group.lean)
* [group_power](group_power.lean) : nat and int powers
* [group_bigops](group_bigops.lean) : products and sums over finsets
* [group_set_bigops](group_set_bigops.lean) : products and sums over finite sets
* [ring](ring.lean)
* [ordered_group](ordered_group.lean)
* [ordered_ring](ordered_ring.lean)
* [ring_power](ring_power.lean) : power in ring structures
* [field](field.lean)
* [ordered_field](ordered_field.lean)
* [category](category/category.md) : category theory

We set a low priority for algebraic operations, so that the elaborator tries concrete structures first.