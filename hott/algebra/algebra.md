algebra
=======

The following files are ported from the standard library. If anything needs to be changed, it is probably a good idea to change it in the standard library and then port the file again (see also [script/port.pl](../../script/port.pl)).

* [binary](binary.hlean) : properties of binary operations
* [relation](relation.hlean) : properties of relations
* [group](group.hlean)
* [ring](ring.hlean)
* [order](order.hlean)
* [ordered_group](ordered_group.hlean)
* [ordered_ring](ordered_ring.hlean)
* [field](field.hlean)

Files which are not ported:

* [hott](hott.hlean) : Basic theorems about the algebraic hierarchy specific to HoTT
* [trunc_group](trunc_group.hlean) : truncate an infinity-group to a group
* [homotopy_group](homotopy_group.hlean) : homotopy groups of a pointed type
* [e_closure](e_closure.hlean) : the type of words formed by a relation

Subfolders:

* [category](category/category.md) : Category Theory
