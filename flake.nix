{
  description = "Lean 4 theorem prover and programming language";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  };

  outputs =
    { nixpkgs, ... }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
      ];

      # Keep in sync with src/CMakeLists.txt LEAN_VERSION_*
      version = "4.31.0-nix";

      eachSystem = nixpkgs.lib.genAttrs systems;

      perSystem = eachSystem (
        system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          inherit (pkgs) lib stdenv;

          setupMimalloc = ''
            mkdir -p mimalloc/src
            cp -r ${pkgs.mimalloc.src} mimalloc/src/mimalloc
            chmod -R u+w mimalloc
          '';

          commonCmakeFlags = [
            "-DCMAKE_BUILD_TYPE=Release"
            "-DUSE_MIMALLOC=ON"
            "-DLEAN_SPECIAL_VERSION_DESC=nix"
            "-DLEAN_EXTRA_CXX_FLAGS=-Wno-array-bounds"
          ];

          mkLeanDerivation =
            attrs:
            stdenv.mkDerivation (
              {
                nativeBuildInputs = [
                  pkgs.cmake
                  pkgs.git
                  pkgs.pkg-config
                ];
                buildInputs = [
                  pkgs.gmp
                  pkgs.libuv
                ];
                preBuild = "patchShebangs .";
                preInstall = "rm -f src/lean";
              }
              // attrs
            );

          srcFiles = lib.fileset.toSource {
            root = ./.;
            fileset = lib.fileset.unions [
              ./src
              ./LICENSE
              ./LICENSES
            ];
          };

          # Assert that the Nix-side version matches what CMake configured.
          checkVersion = ''
            cmake_version=$(sed -n 's/.*LEAN_VERSION_STRING "\(.*\)"/\1/p' include/lean/version.h)
            if [ "$cmake_version" != "${version}" ]; then
              echo "error: flake.nix version (${version}) != CMake version ($cmake_version)"
              echo "Update the 'version' variable in flake.nix to match src/CMakeLists.txt"
              exit 1
            fi
          '';

          # Same derivation as stage1 but with a different mainProgram for `nix run`.
          mkToolAlias =
            name:
            stage1
            // {
              meta = stage1.meta // {
                mainProgram = name;
              };
            };

          stage0 = mkLeanDerivation {
            pname = "lean-stage0";
            inherit version;
            src = lib.fileset.toSource {
              root = ./.;
              fileset = ./stage0;
            };
            sourceRoot = "source/stage0/src";
            preConfigure = setupMimalloc;
            cmakeFlags = commonCmakeFlags ++ [
              "-DSTAGE=0"
              "-DUSE_GITHASH=OFF"
            ];
            meta.license = lib.licenses.asl20;
            meta.platforms = lib.platforms.linux;
          };

          stage1 = mkLeanDerivation {
            pname = "lean";
            inherit version;
            src = srcFiles;
            sourceRoot = "source/src";
            preConfigure = setupMimalloc;
            postConfigure = checkVersion;
            # Stage2 needs these from PREV_STAGE; default install rules exclude them.
            postInstall = ''
              mkdir -p $out/runtime $out/lib/temp
              cp runtime/libleanrt_initial-exec.a $out/runtime/
              cp lib/temp/libleancpp_1.a $out/lib/temp/
            '';
            cmakeFlags = commonCmakeFlags ++ [
              "-DSTAGE=1"
              "-DPREV_STAGE=${stage0}"
              "-DUSE_GITHASH=OFF"
              "-DINSTALL_LICENSE=ON"
              "-DINSTALL_CADICAL=ON"
              "-DUSE_LAKE=ON"
              "-DLEAN_BUILD_TESTS=OFF"
            ];
            meta = {
              description = "Lean 4 theorem prover and programming language";
              homepage = "https://lean-lang.org";
              license = lib.licenses.asl20;
              platforms = lib.platforms.linux;
              mainProgram = "lean";
            };
          };

          stage2 = mkLeanDerivation {
            pname = "lean-stage2";
            inherit version;
            src = srcFiles;
            sourceRoot = "source/src";
            preConfigure = setupMimalloc;
            cmakeFlags = commonCmakeFlags ++ [
              "-DSTAGE=2"
              "-DPREV_STAGE=${stage1}"
              "-DUSE_GITHASH=OFF"
              "-DINSTALL_LICENSE=ON"
              "-DINSTALL_CADICAL=ON"
              "-DUSE_LAKE=ON"
              "-DLEAN_BUILD_TESTS=OFF"
            ];
            meta = {
              description = "Lean 4 stage2 self-hosted toolchain";
              license = lib.licenses.asl20;
              platforms = lib.platforms.linux;
              mainProgram = "lean";
            };
          };

          # Shared between the dev shell and the configure/build apps so a
          # standalone `nix run` finds gmp/libuv via CMAKE_PREFIX_PATH and the
          # dev shell pulls in the same toolchain. Both the `dev` (headers) and
          # default (lib) outputs are needed: cmake's find_path/find_library
          # searches each prefix's include/ and lib/ directories.
          cmakeBuildDeps = [
            pkgs.gmp
            pkgs.gmp.dev
            pkgs.libuv
            pkgs.libuv.dev
          ];

          cmakeBuildTools = [
            pkgs.cmake
            pkgs.pkg-config
            pkgs.llvmPackages.bintools
            pkgs.llvmPackages.clang
            pkgs.llvmPackages.llvm
          ];

          cmakePrefixPath = lib.concatStringsSep ":" (map toString cmakeBuildDeps);

          # cmake's include_directories() silently drops paths that are
          # already in CMAKE_PREFIX_PATH (treated as implicit). The Nix
          # stdenv would normally set NIX_CFLAGS_COMPILE/NIX_LDFLAGS so the
          # clang wrapper injects -isystem/-L; we replicate that here for
          # standalone use outside a derivation.
          nixCflagsCompile = lib.concatStringsSep " " (
            map (dep: "-isystem ${dep}/include") [
              pkgs.gmp.dev
              pkgs.libuv.dev
            ]
          );
          nixLdflags = lib.concatStringsSep " " (
            map (dep: "-L${dep}/lib") [
              pkgs.gmp
              pkgs.libuv
            ]
          );

          # Env exports shared by configure and build scripts: prefix path
          # for find_package, plus the wrapper-bound NIX_* flags.
          commonShellEnv = ''
            export CMAKE_PREFIX_PATH="${cmakePrefixPath}''${CMAKE_PREFIX_PATH:+:$CMAKE_PREFIX_PATH}"
            export NIX_CFLAGS_COMPILE="${nixCflagsCompile}''${NIX_CFLAGS_COMPILE:+ $NIX_CFLAGS_COMPILE}"
            export NIX_LDFLAGS="${nixLdflags}''${NIX_LDFLAGS:+ $NIX_LDFLAGS}"
            export CC=clang
            export CXX=clang++
            export CMAKE_C_COMPILER_LAUNCHER=ccache
            export CMAKE_CXX_COMPILER_LAUNCHER=ccache
          '';

          # Mimalloc is staged at build/mimalloc/src/mimalloc so cmake's
          # ${LEAN_BINARY_DIR}/../mimalloc reference (LEAN_BINARY_DIR is
          # build/release here) resolves correctly.
          configureScript = pkgs.writeShellApplication {
            name = "lean-configure";
            runtimeInputs = cmakeBuildTools ++ cmakeBuildDeps ++ [ pkgs.ccache ];
            text = ''
              ${commonShellEnv}
              mkdir -p build/mimalloc/src
              cp -r ${pkgs.mimalloc.src} build/mimalloc/src/mimalloc
              chmod -R u+w build/mimalloc
              rm -f build/release/CMakeCache.txt
              cmake -S src -B build/release ${
                lib.concatMapStringsSep " " lib.escapeShellArg commonCmakeFlags
              } -DSTAGE=1 -DPREV_STAGE=${stage0} -DUSE_GITHASH=OFF
            '';
          };

          buildScript = pkgs.writeShellApplication {
            name = "lean-build";
            runtimeInputs = cmakeBuildTools ++ cmakeBuildDeps ++ [ pkgs.ccache ];
            text = ''
              ${commonShellEnv}
              cmake --build build/release -- -j"$(nproc)"
            '';
          };

        in
        {
          packages = {
            inherit stage0 stage1 stage2;
            default = stage1;
            lean = mkToolAlias "lean";
            lake = mkToolAlias "lake";
            leanc = mkToolAlias "leanc";
            leanchecker = mkToolAlias "leanchecker";
            leanmake = mkToolAlias "leanmake";
          };

          apps = {
            configure = {
              type = "app";
              program = lib.getExe configureScript;
            };
            buildCMake = {
              type = "app";
              program = lib.getExe buildScript;
            };
          };

          devShells.default =
            (pkgs.mkShell.override {
              stdenv = pkgs.overrideCC stdenv pkgs.llvmPackages.clang;
            })
              {
                buildInputs =
                  cmakeBuildTools
                  ++ cmakeBuildDeps
                  ++ [
                    pkgs.ccache
                    pkgs.gdb
                    pkgs.tree
                  ];
                hardeningDisable = [ "all" ];
                MAKEFLAGS = "-j$(nproc)";
                CTEST_OUTPUT_ON_FAILURE = 1;
                STAGE0 = stage0;
                # Disable elan so Lake uses the local stage1 binaries directly.
                # Without this, elan intercepts `lake`/`lean` and tries to resolve
                # the `lean4-stage0` toolchain from src/lean-toolchain, which fails.
                ELAN = "";
                # Use ccache by name so cmake doesn't cache absolute nix store paths
                CMAKE_C_COMPILER_LAUNCHER = "ccache";
                CMAKE_CXX_COMPILER_LAUNCHER = "ccache";
                shellHook = ''
                  export PATH="$PWD/build/release/bin:$PATH"
                  if [ -f build/release/CMakeCache.txt ] && \
                     ! grep -q "$STAGE0" build/release/CMakeCache.txt 2>/dev/null; then
                    echo "warning: CMakeCache.txt has stale STAGE0 path. Run: nix run .#configure"
                  fi
                '';
              };
        }
      );
    in
    {
      packages = nixpkgs.lib.mapAttrs (_: s: s.packages) perSystem;
      devShells = nixpkgs.lib.mapAttrs (_: s: s.devShells) perSystem;
      apps = nixpkgs.lib.mapAttrs (_: s: s.apps) perSystem;
    };
}
