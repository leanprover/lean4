algebra.category
================

Development of Category Theory. The following files are in this folder (sorted such that files only import previous files).

* [precategory](precategory.hlean)
* [iso](iso.hlean) : iso, mono, epi, split mono, split epi
* [category](category.hlean) : Categories (i.e. univalent or Rezk-complete precategories)
* [groupoid](groupoid.hlean)
* [functor](functor.hlean)
* [nat_trans](nat_trans.hlean) : Natural transformations
* [strict](strict.hlean) : Strict categories
* [constructions](constructions/constructions.md) (subfolder) : basic constructions on categories and examples of categories

The following files depend on some of the files in the folder [constructions](constructions/constructions.md)

* [curry](curry.hlean) : Define currying and uncurrying of functors
* [limits](limits.hlean) : Limits in a category, defined as terminal object in the cone category
* [colimits](colimits.hlean) : Colimits in a category, defined as the limit of the opposite functor
* [adjoint](adjoint.hlean) : Adjoint functors and Equivalences (WIP)
* [yoneda](yoneda.hlean) : Yoneda Embedding (WIP)
