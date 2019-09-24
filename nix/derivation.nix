{ llvmPackages, bash, cmake, python, gmp }:

llvmPackages.stdenv.mkDerivation rec {
  name = "lean-${version}";
  version = "local";

  # I have way too many untracked files in my checkout
  src = builtins.fetchGit { url = ../.; };

  nativeBuildInputs = [ bash cmake python ];
  buildInputs = [ gmp llvmPackages.llvm ];
  enableParallelBuilding = true;

  preConfigure = ''
    cd src
  '';
  postConfigure = ''
    patchShebangs ../../bin
  '';

  meta = with llvmPackages.stdenv.lib; {
    description = "Automatic and interactive theorem prover";
    homepage    = https://leanprover.github.io/;
    license     = licenses.asl20;
    platforms   = platforms.unix;
  };
}
