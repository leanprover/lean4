We port a lot of algebra files from the standard library to the HoTT library.

Port instructions:
- use the script port.pl in scripts/ to port the file. e.g. execute the following in the `scripts` folder: `./port.pl ../library/algebra/lattice.lean ../hott/algebra/lattice.hlean`
- remove imports starting with `data.` or `logic.` (sometimes you need to replace a `data.` import by the corresponding `types.` import)
- Open namespaces `eq` and `algebra` if needed
- (optional) add option `set_option class.force_new true`
- fix all remaining errors. Typical errors include
  - Replacing "and" by "prod" in comments
  - and.intro is replaced by prod.intro, which should be prod.mk.

Currently, the following differences exist between the two libraries, relevant to porting:
- All of the algebraic hierarchy is in the algebra namespace in the HoTT library (on top-level in the standard library).
- The projections "zero" and "one" are reducible in HoTT. This was needed to allow type class inferences to infer
```
H : is_trunc 0 A |- is_trunc (succ (-1)) A
H : is_trunc 1 A |- is_trunc (succ 0) A
```
- Projections of most algebraic structures are definitions instead of theorems in HoTT
- Basic properties of `nat.add` have a simpler proof in HoTT (so that it computes better)