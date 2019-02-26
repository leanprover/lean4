# make gets confused by the .cpp files otherwise
%.lean: ;

%.lean.out: %.lean
	./compile.sh $<

%.hs.out: %.hs
	ghc -O3 $< -o $<.out

%.ml.out: %.ml
	ocamlopt -O3 $< -o $<.out

binarytrees.hs.out: binarytrees.ghc-6.hs
	ghc --make -fllvm -O2 -XBangPatterns -dynamic -threaded -rtsopts  binarytrees.ghc-6.hs -o binarytrees.hs.out

run_binarytrees.hs.out: binarytrees.hs.out
	time ./binarytrees.hs.out +RTS -N4 -K128M -H -RTS 21

binarytrees.ml.out: binarytrees.ocaml-2.ml
	ocamlopt -O3 unix.cmxa binarytrees.ocaml-2.ml -o binarytrees.ml.out

run_binarytrees.ml.out: binarytrees.ml.out
	time ./binarytrees.ml.out 21

run_binarytrees.lean.out: binarytrees.lean.out
	time ./binarytrees.lean.out 21

bench_binarytrees: binarytrees.*.out
	bench "make run_binarytrees.lean.out" "make run_binarytrees.hs.out" "make run_binarytrees.ml.out"

bench_expr_const_folding: expr_const_folding.lean.out expr_const_folding.hs.out expr_const_folding.ml.out
	bench ./expr_const_folding.lean.out ./expr_const_folding.hs.out ./expr_const_folding.ml.out

bench_rbmap: rbmap.lean.out rbmap.hs.out rbmap.ml.out
	bench "./rbmap.lean.out 7000000" "./rbmap.hs.out 7000000" "./rbmap.ml.out 7000000"
