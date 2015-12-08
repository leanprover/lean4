algebra
=======

The following files are [ported](port.md) from the standard library. If anything needs to be changed, it is probably a good idea to change it in the standard library and then port the file again (see also [script/port.pl](../../script/port.pl)).

* [priority](priority.lean) : priority for algebraic operations
* [relation](relation.lean)
* [binary](binary.lean) : binary operations
* [order](order.lean)
* [lattice](lattice.lean)
* [group](group.lean)
* [ring](ring.lean)
* [ordered_group](ordered_group.lean)
* [ordered_ring](ordered_ring.lean)
* [field](field.lean)
* [ordered_field](ordered_field.lean)
* [bundled](bundled.lean) : bundled versions of the algebraic structures

Files which are not ported:

* [hott](hott.hlean) : Basic theorems about the algebraic hierarchy specific to HoTT
* [trunc_group](trunc_group.hlean) : truncate an infinity-group to a group
* [homotopy_group](homotopy_group.hlean) : homotopy groups of a pointed type
* [e_closure](e_closure.hlean) : the type of words formed by a relation

Subfolders (not ported):

* [category](category/category.md) : Category Theory
