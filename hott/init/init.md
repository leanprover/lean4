init
====

The files in this folder are required by low-level operations, and
are always imported by default. You can suppress this behavior by
beginning a file with the keyword "prelude".

Syntax declarations:

* [reserved_notation](reserved_notation.hlean)
* [tactic](tactic.hlean)

Datatypes and logic:

* [logic](logic.hlean)
* [datatypes](datatypes.hlean) (declaration of common types)
* [bool](bool.hlean)
* [num](num.hlean)
* [nat](nat.hlean)
* [function](function.hlean)
* [types](types.hlean) (notation and some theorems for the remaining basic types)

HoTT basics:

* [path](path.hlean)
* [pathover](pathover.hlean) 
* [hedberg](hedberg.hlean)
* [trunc](trunc.hlean)
* [equiv](equiv.hlean)
* [ua](ua.hlean) (declaration of the univalence axiom, and some basic properties)
* [funext](funext.hlean) (proof of equivalence of certain notions of function exensionality, and a proof that function extensionality follows from univalence)

Support for well-founded recursion and automation:

* [relation](relation.hlean)
* [wf](wf.hlean)
* [util](util.hlean)

The default import:

* [default](default.hlean)
