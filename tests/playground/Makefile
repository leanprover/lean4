.PHONY: run_binarytrees.hs.out run_binarytrees.ml.out run_binarytrees.lean.out

binarytrees.hs.out: binarytrees.ghc-6.hs
	ghc --make -fllvm -O2 -XBangPatterns -dynamic -threaded -rtsopts  binarytrees.ghc-6.hs -o binarytrees.hs.out

run_binarytrees.hs.out: binarytrees.hs.out
	time ./binarytrees.hs.out +RTS -N4 -K128M -H -RTS 21

binarytrees.ml.out: binarytrees.ocaml-2.ml
	ocamlopt -O3 unix.cmxa binarytrees.ocaml-2.ml -o binarytrees.ml.out

run_binarytrees.ml.out: binarytrees.ml.out
	time ./binarytrees.ml.out 21

binarytrees.lean: ;

binarytrees.lean.out: binarytrees.lean
	./run.sh binarytrees.lean

run_binarytrees.lean.out: binarytrees.lean.out
	time ./binarytrees.lean.out 21
