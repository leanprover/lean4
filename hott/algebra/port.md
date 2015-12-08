We have ported a lot of algebra files from the standard library to the HoTT library.

Port instructions for the abstract structures:
- use the script port.pl in scripts/ to port the file. e.g. execute in the scripts file:
  `./port.pl ../library/algebra/lattice.lean ../hott/algebra/lattice.hlean`
- remove imports starting with `data.` or `logic.`
- open namespace algebra, and put every identifier in namespace algebra
- add option `set_option class.force_new true`
- fix all remaining errors (open namespace `eq` if needed)
