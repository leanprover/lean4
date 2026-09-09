{
  description = "Lean development flake. Not intended for end users.";

  # We use channels so we're not affected by GitHub's rate limits
  inputs.nixpkgs.url = "https://channels.nixos.org/nixos-unstable/nixexprs.tar.xz";
  # old nixpkgs used for portable release with older glibc (2.27)
  inputs.nixpkgs-old.url = "https://channels.nixos.org/nixos-19.03/nixexprs.tar.xz";
  inputs.nixpkgs-old.flake = false;
  # old nixpkgs used for portable release with older glibc (2.26)
  inputs.nixpkgs-older.url = "https://channels.nixos.org/nixos-18.03/nixexprs.tar.xz";
  inputs.nixpkgs-older.flake = false;

  outputs = inputs: builtins.foldl' inputs.nixpkgs.lib.attrsets.recursiveUpdate {} (builtins.map (system:
    let
      pkgs = import inputs.nixpkgs { inherit system; };
      # An old nixpkgs for creating releases with an old glibc
      pkgsDist-old = import inputs.nixpkgs-older { inherit system; };
      # An old nixpkgs for creating releases with an old glibc
      pkgsDist-old-aarch = import inputs.nixpkgs-old { localSystem.config = "aarch64-unknown-linux-gnu"; };

      llvmPackages = pkgs.llvmPackages_19;

      devShellWithDist = pkgsDist: pkgs.mkShell.override {
          stdenv = pkgs.overrideCC pkgs.stdenv llvmPackages.clang;
        } ({
          buildInputs = with pkgs; [
            cmake gmp libuv ccache pkg-config openssl openssl.dev
            llvmPackages.bintools  # wrapped lld
            llvmPackages.llvm  # llvm-symbolizer for asan/lsan
            gdb
            tree  # for CI
          ];
          # https://github.com/NixOS/nixpkgs/issues/60919
          hardeningDisable = [ "all" ];
          # more convenient `ctest` output
          CTEST_OUTPUT_ON_FAILURE = 1;
        } // pkgs.lib.optionalAttrs pkgs.stdenv.isLinux (let
          # Build OpenSSL 3 statically using pkgsDist's old-glibc stdenv,
          # so the resulting static libs don't require newer glibc symbols.
          opensslForDist = pkgsDist.stdenv.mkDerivation {
            name = "openssl-static-3.6.0";
            src = pkgs.fetchFromGitHub {
              owner = "openssl";
              repo = "openssl";
              rev = "openssl-3.6.0";
              hash = "sha256-EJnbK9ZMdN2ztTTQtb7VsEQvvbMYnY5HJ2LMJlw5FRg=";
            };
            nativeBuildInputs = [ pkgsDist.perl ];
            configurePhase = ''
              patchShebangs .
              ./config --prefix=$out no-shared no-tests
            '';
            buildPhase = "make -j$NIX_BUILD_CORES";
            installPhase = "make install_sw";
          };
          # nixpkgs-older ships GMP 6.1.2, but Lean requires 6.3.0: earlier versions
          # contain bugs that can make Lean produce unsound results. Reuse pkgsDist's
          # own packaging (fat build on x86, PIC, static), built from the same source
          # as `pkgs.gmp` so releases and development use one GMP version.
          gmpForDist = (pkgsDist.gmp.override { cxx = false; withStatic = true; }).overrideAttrs (attrs: {
            name = "gmp-${pkgs.gmp.version}";
            inherit (pkgs.gmp) src;
            configureFlags = attrs.configureFlags ++ [
              "--disable-shared"
              # nixpkgs 18.03 pins the build triple only on ARM, but GMP's config.guess
              # runtime-probes the CPU via /proc/cpuinfo on x86 too, which is broken on
              # the multicore CI runners.
              "--build=${pkgsDist.stdenv.buildPlatform.config}"
            ];
            doCheck = false;
          } // pkgs.lib.optionalAttrs (pkgs.stdenv.system == "aarch64-linux") {
            # would need additional linking setup on Linux aarch64, we don't use it anywhere else either
            hardeningDisable = [ "stackprotector" ];
          });
        in {
          GMP = gmpForDist;
          LIBUV = pkgsDist.libuv.overrideAttrs (attrs: {
            configureFlags = ["--enable-static"];
            hardeningDisable = [ "stackprotector" ];
            # Sync version with CMakeLists.txt
            version = "1.48.0";
            src = pkgs.fetchFromGitHub {
              owner = "libuv";
              repo = "libuv";
              rev = "v1.48.0";
              sha256 = "100nj16fg8922qg4m2hdjh62zv4p32wyrllsvqr659hdhjc03bsk";
            };
            doCheck = false;
          });
          OPENSSL = opensslForDist;
          OPENSSL_DEV = opensslForDist;
          GLIBC = pkgsDist.glibc;
          GLIBC_DEV = pkgsDist.glibc.dev;
          GCC_LIB = pkgsDist.gcc.cc.lib;
          ZLIB = pkgsDist.zlib;
          # for CI coredumps
          GDB = pkgsDist.gdb;
        }));
    in {
      devShells.${system} = {
        # The default development shell for working on lean itself
        default = devShellWithDist pkgs;
        oldGlibc = devShellWithDist pkgsDist-old;
        oldGlibcAArch = devShellWithDist pkgsDist-old-aarch;
      };
    }) ["x86_64-linux" "aarch64-linux" "aarch64-darwin"]);
}
