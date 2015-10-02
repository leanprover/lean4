algebra.category.constructions
==============================

Common categories and constructions on categories. The following files are in this folder.

* [functor](functor.hlean) : Functor category
* [opposite](opposite.hlean) : Opposite category
* [hset](hset.hlean) : Category of sets. Prove that it is complete and cocomplete
* [sum](sum.hlean) : Sum category
* [product](product.hlean) : Product category
* [comma](comma.hlean) : Comma category
* [cone](cone.hlean) : Cone category

Discrete, indiscrete or finite categories:

* [finite_cats](finite_cats.hlean) : Some finite categories, which are diagrams of common limits (the diagram for the pullback or the equalizer). Also contains a general construction of categories where you give some generators for the morphisms, with the condition that you cannot compose two of thosex
* [discrete](discrete.hlean)
* [indiscrete](indiscrete.hlean)
* [terminal](terminal.hlean)
* [initial](initial.hlean)

Non-basic topics:
* [functor2](functor2.hlean) : showing that the functor category has (co)limits if the codomain has them.
