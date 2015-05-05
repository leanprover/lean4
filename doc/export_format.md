Low level format
================

Lean can export .lean and .hlean files in a low-level format that is easy to parse and process.
The exported file contains only fully elaborated terms.
The file describes hierarchical names, universe levels and expressions.
These objects are used to declare inductive datatypes, definitions and axioms.

Hierarchical names
------------------

A hierarchical name is essentially a list of strings and integers.
Each hierarchical name has a unique identifier: a unsigned integer.
The unsigned integer 0 denotes the _anonymous_ hierarchical name.
We can also view it as the empty name.
The following commands are used to define hierarchical names in the export file.

```
<nidx'> s <nidx> <string>
<nidx'> i <nidx> <integer>
```

In both commands, `nidx` is the unique identifier of an existing hierarchical name,
and `nidx'` is the identifier for the hierarchical name being defined.
The first command defines a hierarchical name by appending the given string,
and the second by appending the given integer.
The hierarchical name `foo.bla.1.boo` may be defined using the following sequence of commands

```
1 s 0 foo
2 s 1 bla
3 i 2 1
4 s 3 boo
```

Universe terms
---------------

Lean supports universe polymorphism.
That is, declaration in Lean can be parametrized by one or more universe level parameters.
The declarations can then be instantiated with universe level expressions.
In the standard Lean front-end, universe levels can be omitted, and the Lean elaborator (tries) to infer them automatically for users.
In this section, we describe the commands for create universe terms.
Each universe term has a unique identifier: a unsigned integer.
Note that the identifiers assigned to universe terms and hierarchical names are not disjoint.
The unsigned integer 0 is used to denote the universe 0.

The following commands are used to create universe terms in the export file.

```
<uidx'> US  <uidx>
<uidx'> UM  <uidx_1> <uidx_2>
<uidx'> UIM <uidx_1> <uidx_2>
<uidx'> UP  <nidx>
<uidx'> UG  <nidx>
```

In the commands above, `uidx`, `uidx_1` and `uidx_2` denote the unique identifier of existing universe terms,
`nidx` the unique identifier of existing hierarchical names, and `nidx'` is the identifier for the universe
term being defined. The command `US` defines the _successor_ universe for `uidx`, the `UM` the maximum universe for `uidx_1` and `uidx_2`,
and `UIM` is the "impredicative" maximum. It is defined as zero if `uidx_2` evaluates to zero, and `UM` otherwise.
The command `UP` defines the universe parameter with name `nidx`, and `UG` the global universe with name `nidx`.
Here is the sequence of commands for creating the universe term `imax (max 2 l1) l2`.
```
1 s 0 l1
2 s 0 l2
1 US 0
2 US 1
3 UP 1
4 UP 2
5 UM 2 3
6 UIM 5 4
```
Thus, the unique identifier for term `imax (max 2 l1) l2` is `6`. The unique identifier for term `l1` is `3`.

Expressions
-----------

In Lean, we have the following kind of expressions:
variables, sorts (aka Type), constants, constants, function applications, lambdas, and dependent function spaces (aka Pis).
Each expression has a unique identifier: a unsigned integer.
Again, the expression unique identifiers are not disjoint from the universe term and hierarchical name ones.
The following command are used to create expressions in the export file.
```
<eidx'> V <integer>
<eidx'> S <uidx>
<eidx'> C <nidx> <uidx>*
<eidx'> A <eidx_1> <eidx_2>
<eidx'> L <info> <nidx> <eidx_1> <eidx_2>
<eidx'> P <info> <nidx> <eidx_1> <eidx_2>
```
In the commands above, `uidx` denotes the unique identifier of existing universe terms,
`nidx` the unique identifier of existing hierarchical names, `eidx_1` and `eidx_2` the unique
identifier of existing expressions, `info` is an annotation (explained later), and
`eidx'` is the identifier for the expression being defined.
The command `V` defines a bound variable with de Bruijn index `<integer>`.
The command `S` defines a sort using the given universe term.
The command `C` defines a constant with hierarchical name `nidx` and instantiated with 0 or more
universe terms `<uidx>*`.
The command `A` defines function application where `eidx_1` is the function, and `eidx_2` is the argument.
The binders of lambda and Pi abstractions are decorated with `info`.
This information has no semantic value for fully elaborated terms, but it is useful for pretty printing.
`info` can be one of the following annotations: `D`, `I`, `S` and `C`. The annotation `D` corresponds to
the default binder annotation `(...)` used in `.lean` files, and `I` to `{...}`, `S` to `{{...}}`, and
`C` to `[...]`.
The command `L` defines a lambda abstraction where `nidx` is the binder name, `eidx_1` the type, and
`eidx_2` the body. The command `P` is similar to `L`, but defines a Pi abstraction.
Here is the sequence of commands for creating the term `fun {A : Type.{1}} (a : A), a`
```
1 s 0 A
2 s 1 a
1 US 0
1 S 1
2 V 0
3 L D 2 2
4 L I 1 3
```
Now, assume the environment contains the following constant declarations:
`nat : Type.{1}`, `nat.zero : nat`, `nat.succ : nat -> nat`, and `vector.{l} : Type.{l} -> nat -> Type.{max 1 l}`.
Then, the following sequence of commands can be used to create the term `vector.{1} nat 3`.
We annotate some commands with comments of the form `-- ...` to make the example easier to understand.
```
1 s 0 nat
2 s 1 zero
3 s 1 succ
4 s 0 vector
1 US 0
1 C 2          -- nat.zero
2 C 3          -- nat.succ
3 A 2 1        -- nat.succ nat.zero
4 A 2 3        -- nat.succ (nat.succ nat.zero)
5 A 2 4        -- nat.succ (nat.succ (nat.succ nat.zero))
6 C 4 1        -- vector.{1}
7 C 1          -- nat
8 A 6 7        -- vector.{1} nat
9 A 8 5        -- vector.{1} nat (nat.succ (nat.succ (nat.succ nat.zero)))
```

Imported files
--------------

As `.lean` and `.hlean` files, the exported files may import other exported files.
The _import_ commands can be relative or absolute paths (with respect to the `LEAN_PATH` environment variable).
```
DI <nidx>
RI <integer> <nidx>
```
Paths are described using hierarchical names. The hierarchical name `foo.bla.boo` corresponds to the path `foo/bla/boo`.
The command `DI` is the direct import, it instructs the reader to import the file at the location corresponding to
the hierarchical name `nidx`. The command `RI` is the relative import, the integer represents how many `../` should be added the path
represented by the hierarchical name `nidx`.

Global universe level declaration
---------------------------------

The command
```
UNI <nidx>
```
declares a global universe with name `nidx`.

Definitions and Axioms
----------------------

The command
```
DEF <nidx> <nidx>* | <eidx_1> <edix_2>
```
declares a definition with name `nidx` with zero or more universe parameters named `<nidx>*`.
The type is given by the expression `eidx_1` and the value by `eidx_2`.
Axioms are declared in a similar way
```
AX <nidx> <nidx>* | <eidx>
```
We are postulating the existence of an element with the given type.
The following command declare the `definition id.{l} {A : Type.{l}} (a : A) : A := a`.
```
2 s 0 id
3 s 0 l
4 s 0 A
1 UP 3
0 S 1
5 s 0 a
1 V 0
2 V 1
3 P D 5 1 2
4 P I 4 0 3
5 L D 5 1 1
6 L D 4 0 5
DEF 2 3 | 4 6
```

Inductive definitions
---------------------

Mutually inductive datatype declarations are slightly more complicated.
They are declared by a block of commands delimited by the command `BIND` and `EIND`.
The command `BIND` has the following form:
```
BIND <integer> <integer> <nidx>*
```
where the first integer are the number of parameters, the second is the number of
mutually recursive types being declared by the block, and `nidx*` is the sequence
of universe parameter _names_.
The command `EIND` is just a delimiter and does not have arguments.
The block is composed by commands `IND` and `INTRO`.
```
IND <nidx> <eidx>
INTRO <nidx> <eidx>
```
The command `IND` declares an inductive type with name `nidx` and type `eidx`.
The command `INTRO` declares an introduction rule (aka constructor) with name
`nidx` and type `eidx`. The first command in a block is always an `IND`,
the subsequent `INTRO` commands are declaring the introduction rules for this
inductive type.

For example, the following mutually recursive declaration
```lean
inductive tree.{l} (A : Type.{l}) : Type.{max 1 l} :=
| node  : tree_list.{l} A → tree.{l} A
| empty : tree.{l} A
with tree_list : Type.{max 1 l} :=
| nil  : tree_list.{l} A
| cons : tree.{l} A → tree_list.{l} A → tree_list.{l} A
```
is encoded by the following sequence of commands
```
2 s 0 l
3 s 0 tree
4 s 0 A
1 UP 2
0 S 1
2 US 0
3 UM 2 1
1 S 3
2 P D 4 0 1
5 s 3 node
6 s 0 a
7 s 0 tree_list
3 C 7 1
4 V 0
5 A 3 4
6 C 3 1
7 V 1
8 A 6 7
9 P D 6 5 8
10 P I 4 0 9
8 s 3 empty
11 A 6 4
12 P D 4 0 11
9 s 7 nil
13 P D 4 0 5
10 s 7 cons
14 A 3 7
15 V 2
16 A 3 15
17 P D 6 14 16
18 P D 6 11 17
19 P I 4 0 18
BIND 1 2 2
IND 3 2
INTRO 5 10
INTRO 8 12
IND 7 2
INTRO 9 13
INTRO 10 19
EIND
```

Exporting declarations
----------------------

The command line option `-E filename` is used to export declarations
in the format described above.
