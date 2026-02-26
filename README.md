# Lean

**Fork of the [official Lean repo](https://github.com/leanprover/lean4) focused on making life easier for terminal-only Lean developers.**

Features added compared to upstream:

- Installation of standalone Lake binaries with `lake install` and `lake install --git`
- Lean formatter integrated with LSP server
- Notifications instead of diagnostics during LSP server setup
- Concise error messages when lake build at LSP setup fails
- Opening up of diagnostic fix creation by users for better linters

Improvements for reproducible builds and development shell:

- Build stage caching in `flake.nix` for [Nix package manager](https://wiki.nixos.org/wiki/Flake) users: separated `stage0` (C-only) and `stage1` (Lean) build
- Configuration of `ccache` in Nix `devshell`
- Added public shared cache for stage compilation artifacts

<!--toc:start-->

- [Lean](#lean)
  - [Installation](#installation)
  - [Usage](#usage)
    - [As Flake Input](#as-flake-input)
    - [Without Installation](#without-installation)
  - [Development](#development)
    - [Structure](#structure)
    - [Building for Nix](#building-for-nix)
    - [Caching `stage0` with Nix](#caching-stage0-with-nix)
    - [Development Builds](#development-builds)
    - [LSP for Lean Development](#lsp-for-lean-development)
    - [Using with elan](#using-with-elan)
    - [Testing](#testing)
    - [Ignoring Nix `stage0` Cache](#ignoring-nix-stage0-cache)
  - [Related](#related)

<!--toc:end-->

## Installation

Add this repo as a Flake input to any of your Flake-based Nix projects:

```nix
{
  inputs.lean4.url = "github:wvhulle/lean4";

  outputs = { nixpkgs, lean4, ... }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
      lean = lean4.packages.x86_64-linux;
    in {
      devShells.x86_64-linux.default = pkgs.mkShell {
        packages = [ lean.lean ];
      };
    };
}
```

## Usage

### As Flake Input

Just add a `flake.nix` with this repo as input.

```nix
{

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    lean4.url = "github:wvhulle/lean4";
    lean4-nix.url = "github:lenianiva/lean4-nix";
  };

  outputs =
    {
      self,
      nixpkgs,
      lean4,
      lean4-nix,
    }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs {
        inherit system;
        config.allowUnfree = true;
      };

      lake2nix = pkgs.callPackage lean4-nix.lake {
        lean = {
          lean-all = lean4.packages.${system}.lake;
        };
      };

    in
    {
      packages.${system}.default = lake2nix.mkPackage {
        name = "lean-prism";
        src = ./.;
      };

      devShells.${system} = {
        default = pkgs.mkShell {
          packages = with pkgs; [
            lean4.packages.${system}.lake
          ];

        };

        # Optional: only if you have a local checkout of the lean4 repo.
        # Use locally-built lean4 — no flake rebuild on source changes.
        # Requires: make -j -C ../lean4/build/release
        local = pkgs.mkShell {
          packages = with pkgs; [
            gcc
            llvmPackages.bintools
          ];

          shellHook = ''
            export PATH="$PWD/../lean4/build/release/stage1/bin:$PATH"
          '';
        };
      };
    };
}
```

The Nix flake outputs the same binaries as upstream, but just packages that in isolated Nix packages:

| Package                                                                                        | Description                                    |
| ---------------------------------------------------------------------------------------------- | ---------------------------------------------- |
| `lean`                                                                                         | Lean compiler (alias for `stage1`)             |
| `lake`                                                                                         | Lake build tool (same derivation, runs `lake`) |
| `leanc`                                                                                        | Lean C compiler wrapper                        |
| `leanchecker`                                                                                  | Lean proof checker                             |
| `leanmake`                                                                                     | Lean make tool                                 |
| When you launch your editor and a Lean LSP client, it should get automatic formatting support. |                                                |

### Without Installation

Run the Lean binaries directly without installing them permanently:

- `nix run .#lean`
- `nix run .#lake`

The first time, you can choose between:

- Compiling from scratch: this might take very long as `stage0` needs to be built (+20 minutes). Builds are cached until you do a Nix garbage collection.
- Using the Cachix cache (recommended): downloads prebuilt artifacts

Less commonly used binaries are also included:

- `nix run .#leanc`
- `nix run .#leanchecker`
- `nix run .#leanmake`

## Development

### Structure

The Nix flake outputs are named after upstream conventions. Lean compilation is split into several stages. Each stage is mapped to a Nix build target that can be cached by Nix.

| Package   | C (transpiled) | C++ (runtime) | Lean | Description                          |
| --------- | -------------- | ------------- | ---- | ------------------------------------ |
| `stage0`  | yes            | yes           | no   | Bootstrap compiler                   |
| `stage1`  | no             | yes           | yes  | Full toolchain, compiled by `stage0` |
| `stage2`  | no             | yes           | yes  | Verification rebuild by `stage1`     |
| `default` |                |               |      | Alias for `stage1`                   |

All tool packages (`lean`, `lake`, `leanc`, `leanchecker`, `leanmake`) are the same derivation with a different entry point. Building any one of them gives you the complete toolchain.

### Building for Nix

You can build for example `stage0` with:

```bash
nix build .#stage0
```

To build and simultaneously push artifacts to Cachix so others can have quicker builds:

```bash
cachix watch-exec wvhulle -- nix build .#stage0
```

To push an already-built result afterward:

```bash
nix build .#stage0 --print-out-paths | cachix push wvhulle
```

### Caching `stage0` with Nix

`nix build` always builds from scratch in a sandbox. Use the Nix dev shell when working on the Lean codebase (and ignoring the part of `stage0`):

```bash
nix develop
```

This might take awhile, since Nix will build and cache `stage0`.

I recommend installing `direnv` and creating a `.envrc` file:

```bash
use flake
```

Run this configuration step once. It will configurei CMake to use the cached `stage0` (skips ~20min bootstrap):

```bash
cmake -S . -B build/release \
  -DCMAKE_BUILD_TYPE=Release \
  -DUSE_MIMALLOC=ON \
  -DSTAGE1_PREV_STAGE=$STAGE0
```

### Development Builds

After caching `stage0` and running CMake configuration in previous steps once, you can build (and rebuild after editing `src/*`) with:

```bash
make -C build/release stage1
```

The dev shell sets `MAKEFLAGS="-j$(nproc)"` automatically, so all `make` invocations use full parallelism.

### LSP for Lean Development

The `src/lean-toolchain` file references `lean4-stage0`, a toolchain name that only makes sense inside the CMake build system. If elan is on your `PATH`, it intercepts `lake`/`lean` and fails to resolve this toolchain.

The dev shell handles this automatically: it disables elan via `ELAN=""` and prepends `build/release/stage1/bin` to `PATH`. After building stage1, `lake serve` works from within `src/`:

```bash
make -C build/release stage1
cd src && lake serve
```

### Using with elan

If you use elan (outside the Nix dev shell), you can register a local build as a custom toolchain:

```bash
elan toolchain link lean4-local ./build/release/stage1
```

This makes the locally-built stage1 available under the name `lean4-local`. You can then use it in any project by setting the `lean-toolchain` file:

```
lean4-local
```

Or override it for a single command:

```bash
elan run --install lean4-local lake build
```

To register the Nix-built stage1 instead of a `make` build:

```bash
elan toolchain link lean4-local "$(nix build .#stage1 --print-out-paths)"
```

### Testing

See [doc/dev/testing.md](doc/dev/testing.md) for how to run the test suite, write new tests, and fix broken expected output.

### Ignoring Nix `stage0` Cache

The dev shell sets `$STAGE0` to the Nix-cached stage0 output. To build stage0 from source instead (e.g. when hacking on `stage0/`), omit `-DSTAGE1_PREV_STAGE`:

```bash
cmake -S . -B build/release \
  -DCMAKE_BUILD_TYPE=Release \
  -DUSE_MIMALLOC=ON
```

## Related

This project primarily serves as an easy way for me to hack on the upstream Lean codebase while using Nix.

Try some of my other Lean projects:

- [Lean-TUI](https://codeberg.org/wvhulle/lean-tui): terminal-only info view for proof visualization
- [Heron](https://codeberg.org/wvhulle/heron): comprehensive linter and auto-fixer for Lean
