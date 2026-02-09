This release introduces the Lean module system, which allows files to
control the visibility of their contents for other files. In previous
releases, this feature was available as a preview when the option
`experimental.module` was set to `true`; it is now a fully supported
feature of Lean.

# Benefits

Because modules reduce the amount of information exposed to other
code, they speed up rebuilds because irrelevant changes can be
ignored, they make it possible to be deliberate about API evolution by
hiding details that may change from clients, they help proofs be
checked faster by avoiding accidentally unfolding definitions, and
they lead to smaller executable files through improved dead code
elimination.

# Visibility

A source file is a module if it begins with the `module` keyword.  By
default, declarations in a module are private; the `public` modifier
exports them. Proofs of theorems and bodies of definitions are private
by default even when their signatures are public; the bodies of
definitions can be made public by adding the `@[expose]`
attribute. Theorems and opaque constants never expose their bodies.

`public section` and `@[expose] section` change the default visibility
of declarations in the section.

# Imports

Modules may only import other modules. By default, `import` adds the
public information of the imported module to the private scope of the
current module. Adding the `public` modifier to an import places the
imported modules's public information in the public scope of the
current module, exposing it in turn to the current module's clients.

Within a package, `import all` can be used to import another module's
private scope into the current module; this can be used to separate
lemmas or tests from definition modules without exposing details to
downstream clients.

# Meta Code

Code used in metaprograms must be marked `meta`. This ensures that the
code is compiled and available for execution when it is needed during
elaboration. Meta code may only reference other meta code. A whole
module can be made available in the meta phase using `meta import`;
this allows code to be shared across phases by importing the module in
each phase. Code that is reachable from public metaprograms must be
imported via `public meta import`, while local metaprograms can use
plain `meta import` for their dependencies.


The module system is described in detail in [the Lean language reference](https://lean-reference-manual-review.netlify.app/find/?domain=Verso.Genre.Manual.section&name=files).
