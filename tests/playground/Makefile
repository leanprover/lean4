#BENCH=./bad_bench
BENCH=bench

# make gets confused by the .cpp files otherwise
%.lean: ;

%.lean.out: %.lean ../compiler/test_flags.sh
	./compile.sh $<

%.hs.out: %.hs
	ghc -fllvm -O3 $< -o $<.out

%.ml.out: %.ml
	ocamlopt -O3 $< -o $<.out

binarytrees.hs.out: binarytrees.ghc-6.hs
	ghc --make -fllvm -O2 -XBangPatterns -dynamic -threaded -rtsopts  binarytrees.ghc-6.hs -o binarytrees.hs.out

run_binarytrees.hs.out: binarytrees.hs.out
	time ./binarytrees.hs.out +RTS -N4 -K128M -H -RTS 21

binarytrees.ml.out: binarytrees.ocaml-2.ml
	ocamlopt -noassert -unsafe -fPIC -nodynlink -inline 100 -O3 unix.cmxa binarytrees.ocaml-2.ml -o binarytrees.ml.out

run_binarytrees.ml.out: binarytrees.ml.out
	time ./binarytrees.ml.out 21

run_binarytrees.lean.out: binarytrees.lean.out
	time ./binarytrees.lean.out 21

bench_deriv: deriv.lean.out deriv.hs.out deriv.ml.out
	$(BENCH) ./deriv.lean.out ./deriv.hs.out ./deriv.ml.out

bench_binarytrees: binarytrees.lean.out binarytrees.hs.out binarytrees.ml.out
	$(BENCH) "make run_binarytrees.lean.out" "make run_binarytrees.hs.out" "make run_binarytrees.ml.out"

bench_expr_const_folding: expr_const_folding.lean.out expr_const_folding.hs.out expr_const_folding.ml.out
	$(BENCH) ./expr_const_folding.lean.out ./expr_const_folding.hs.out ./expr_const_folding.ml.out

bench_rbmap: rbmap.lean.out rbmap.hs.out rbmap.ml.out
	$(BENCH) "./rbmap.lean.out 7000000" "./rbmap.hs.out 7000000" "./rbmap.ml.out 7000000"

bench_all: bench_deriv bench_binarytrees bench_expr_const_folding bench_rbmap

run_frontend:
	cd ../.. && time bin/lean --new-frontend library/init/core.lean

bench_lean: deriv.lean.out expr_const_folding.lean.out rbmap.lean.out binarytrees.lean.out ../../bin/lean unionfind1.lean.out unionfind2.lean.out
	$(BENCH) ./deriv.lean.out ./expr_const_folding.lean.out "./rbmap.lean.out 7000000" "./binarytrees.lean.out 21" "make run_frontend" "./unionfind1.lean.out 3000000" "./unionfind2.lean.out 3000000"
