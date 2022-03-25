This is the repository for **Lean 4**, which is currently being released as milestone releases towards a first stable release.
[Lean 3](https://github.com/leanprover/lean) is still the latest stable release.

# About

- [Quickstart](https://github.com/leanprover/lean4/blob/master/doc/quickstart.md)
- [Homepage](https://leanprover.github.io)
- [Theorem Proving Tutorial](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Manual](https://leanprover.github.io/lean4/doc/)
- [Release notes](RELEASES.md) starting at v4.0.0-m3
- [FAQ](https://leanprover.github.io/lean4/doc/faq.html)

# Installation

See [Setting Up Lean](https://leanprover.github.io/lean4/doc/setup.html).

## Supported Platforms

### Tier 1

Platforms built & tested by our CI, available as nightly & stable releases via elan (see above)

* x86-64 Linux with glibc 2.27+
* x86-64 macOS 10.15+
* x86-64 Windows 10+

### Tier 2

Platforms cross-compiled but not tested by our CI, available as nightly & stable releases

Releases may be silently broken due to the lack of automated testing.
Issue reports and fixes are welcome.

* aarch64 Linux with glibc 2.27+

### Tier 3

Platforms that are known to work from manual testing, but do not come with CI or official releases

* aarch64 (M1) macOS - may also [use x86-64 releases via Rosetta](https://github.com/leanprover/elan#manual-installation)

# Contributing

Please read our [Contribution Guidelines](CONTRIBUTING.md) first.

# Building from Source

See [Building Lean](https://leanprover.github.io/lean4/doc/make/index.html).
