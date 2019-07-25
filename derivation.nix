{ clangStdenv, cmake, llvm, python, gmp }:

clangStdenv.mkDerivation rec {
  name = "lean-${version}";
  version = "local";

  # I have way too many untracked files in my checkout
  src = builtins.fetchGit { url = ./.; };

  nativeBuildInputs = [ cmake python ];
  buildInputs = [ gmp llvm ];
  enableParallelBuilding = true;

  preConfigure = ''
    cd src
  '';
  postConfigure = ''
    patchShebangs ../../bin
  '';

  meta = with clangStdenv.lib; {
    description = "Automatic and interactive theorem prover";
    homepage    = https://leanprover.github.io/;
    license     = licenses.asl20;
    platforms   = platforms.unix;
  };
}
