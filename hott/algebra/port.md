We port a lot of algebra files from the standard library to the HoTT library.

Port instructions:
- use the script port.pl in scripts/ to port the file. e.g. execute the following in the `scripts` folder: `./port.pl ../library/algebra/lattice.lean ../hott/algebra/lattice.hlean`
- remove imports starting with `data.` or `logic.` (sometimes you need to replace a `data.` import by the corresponding `types.` import)
- All of the algebraic hierarchy is in the algebra namespace in the HoTT library.
- Open namespaces `eq` and `algebra` if needed
- (optional) add option `set_option class.force_new true`
- fix all remaining errors. Typical errors include
  - Replacing "and" by "prod" in comments
  - and.intro is replaced by prod.intro, which should be prod.mk.
