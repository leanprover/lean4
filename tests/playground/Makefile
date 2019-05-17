## CONFIG

BENCH=ulimit -s unlimited && bench
CROSS_BENCHES = binarytrees deriv expr_const_folding rbmap rbmap_shared

# basic version usable without Nix
#CROSS_CATS = .lean .perf.lean .hs .gc.hs .perf.hs .llvm.hs .ml .gc.ml .perf.ml
CROSS_CATS = .lean .lean.perf .gcc.lean .hs .gc.hs .hs.perf .llvm.hs .ml .gc.ml .ml.perf .flambda.ml

GHC_FLAGS = -O3
OCAML_FLAGS = -O3

## IMPLEMENTATION

CROSS_INPUTS = $(foreach bench,$(CROSS_BENCHES), $(foreach cat, $(CROSS_CATS), $(bench)$(cat)))

LEAN_BIN ?= ../../bin
GHC ?= ghc
OCAML ?= ocamlopt.opt

.SECONDARY: $(CROSS_INPUTS:%=%.out) $(CROSS_INPUTS:%=bench/%.bench)
.DELETE_ON_ERROR:

all: report_cross.csv

# disable some built-in rules
%.lean:
%.out: %

%.lean.cpp: %.lean
	$(LEAN_BIN)/lean --cpp=$@ $<
%.lean.out: %.lean.cpp
	$(LEAN_BIN)/leanc -o $@ $<
# Binaries x.lean.out and x.gcc.lean.out etc. are produced by the
# same rules and x.lean source file by copying the latter to
# x.gcc.lean. This also avoids conflicts between intermediate
# files of the two binaries.
%.gcc.lean.out: LEAN_BIN = $(LEAN_GCC_BIN)
%.gcc.lean: %.lean; ln -f $< $@

%.hs.out: %.hs
	$(GHC) $(GHC_FLAGS) -rtsopts $< -o $@
%.llvm.hs.out: GHC_FLAGS += -fllvm
%.llvm.hs: %.hs; ln -f $< $@

binarytrees.hs: binarytrees.ghc-6.hs; ln -f $< $@
# NOTE: changed `-N4` rtsopt to `-N` to be less system-dependent
binarytrees%hs.out: GHC_FLAGS += --make -O2 -XBangPatterns -dynamic -threaded -rtsopts -with-rtsopts='-N -K128M -H'

%.ml.out: %.ml
	$(OCAML) $(OCAML_FLAGS) $< -o $@
%.gc.ml.out: OCAML_FLAGS += -runtime-variant i
%.gc.ml: %.ml; ln -f $< $@
%.flambda.ml.out: OCAML = $(OCAML_FLAMBDA)
%.flambda.ml: %.ml; ln -f $< $@

binarytrees.ml: binarytrees.ocaml-2.ml; ln -f $< $@
binarytrees%ml.out: OCAML_FLAGS += -noassert -unsafe -fPIC -nodynlink -inline 100 -O3 unix.cmxa

bench:
	-@mkdir bench

bench/%.bench: %.out | bench
	$(BENCH) "./$< $(BENCH_PARAMS)" --json $@

bench/binarytrees.%.bench: BENCH_PARAMS = 21

bench/rbmap.%.bench: BENCH_PARAMS = 7000000

rbmap_shared.%.out: rbmap_checkpoint.%.out; ln -f $< $@
bench/rbmap_shared.%.bench: BENCH_PARAMS = 500000 1

bench/%gc.hs.bench: %hs.out | bench
	./$< +RTS -t --machine-readable -RTS $(BENCH_PARAMS) 2> $@

bench/%gc.ml.bench: %gc.ml.out | bench
	ulimit -s unlimited && OCAML_INSTR_FILE=$@ time -ao $@ -f '%e' ./$< $(BENCH_PARAMS)

bench/%.perf.bench: %.out | bench
	ulimit -s unlimited && perf stat -e cache-references,cache-misses,branches,branch-misses -o $@ ./$< $(BENCH_PARAMS)

# fork() breaks instrumentation
bench/binarytrees.gc.ml.bench:
	touch $@

bench_cross: $(CROSS_INPUTS:%=bench/%.bench)

# yes.
space = $() $()

report_cross.csv: bench_cross report.py
	BENCHES=$(subst $(space),:,$(CROSS_BENCHES)) CATS=$(subst $(space),:,$(CROSS_CATS)) ./report.py > $@

clean:
	-rm *.out bench/*
