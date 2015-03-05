init
====

The modules in this folder are required by low-level operations, and
are always imported by default. You can suppress this behavior by
beginning a file with the keyword "prelude".

Syntax declarations:

* [reserved_notation](reserved_notation.hlean)
* [tactic](tactic.hlean)
* [priority](priority.hlean)

Datatypes and logic:

* [datatypes](datatypes.hlean)
* [logic](logic.hlean)
* [bool](bool.hlean)
* [num](num.hlean)
* [nat](nat.hlean)
* [function](function.hlean)
* [types](types/types.md) (subfolder)

HoTT basics:

* [path](path.hlean)
* [hedberg](hedberg.hlean)
* [trunc](trunc.hlean)
* [equiv](equiv.hlean)
* [axioms](axioms/axioms.md) (subfolder)

Support for well-founded recursion and automation:

* [relation](relation.hlean)
* [wf](wf.hlean)
* [util](util.hlean)

The default import:

* [default](default.hlean)

