## CONFIG

BENCH=ulimit -s unlimited && bench
CROSS_BENCHES = binarytrees deriv expr_const_folding rbmap

# basic version usable without Nix
#CROSS_CATS = .lean .hs .llvm.hs .ml
CROSS_CATS = .lean .gcc.lean .hs .llvm.hs .ml .flambda.ml

GHC_FLAGS = -O3
OCAML_FLAGS = -O3

## IMPLEMENTATION

LEAN_BIN ?= ../../bin
GHC ?= ghc
OCAML ?= ocamlopt.opt

.PRECIOUS: %.out bench/%
.DELETE_ON_ERROR:

all: report_cross.csv

# make gets confused by the .cpp files otherwise
%.lean: ;

%.lean.cpp: %.lean
	$(LEAN_BIN)/lean --cpp=$<.cpp $<
%.lean.out: %.lean.cpp
	$(LEAN_BIN)/leanc -o $@ $<
# Binaries x.lean.out and x.gcc.lean.out etc. are produced by the
# same rules and x.lean source file by copying the latter to
# x.gcc.lean. This also avoids conflicts between intermediate
# files of the two binaries.
%.gcc.lean.out: LEAN_BIN = $(LEAN_GCC_BIN)
%.gcc.lean: %.lean; ln $< $@

%.hs.out: %.hs
	$(GHC) $(GHC_FLAGS) $< -o $@
%.llvm.hs.out: GHC_FLAGS += -fllvm
%.llvm.hs: %.hs; ln $< $@

binarytrees.hs: binarytrees.ghc-6.hs; ln $< $@
# NOTE: changed `-N4` rtsopt to `-N` to be less system-dependent
binarytrees%hs.out: GHC_FLAGS += --make -O2 -XBangPatterns -dynamic -threaded -rtsopts -with-rtsopts='-N -K128M -H'

%.ml.out: %.ml
	$(OCAML) $(OCAML_FLAGS) $< -o $@
%.flambda.ml.out: OCAML = $(OCAML_FLAMBDA)
%.flambda.ml: %.ml; ln $< $@

binarytrees.ml: binarytrees.ocaml-2.ml; ln $< $@
binarytrees%ml.out: OCAML_FLAGS = -noassert -unsafe -fPIC -nodynlink -inline 100 -O3 unix.cmxa

bench:
	-@mkdir bench

bench/%.bench: %.out | bench
	$(BENCH) "./$< $(BENCH_PARAMS)" --json $@

bench/binarytrees.%.bench: BENCH_PARAMS = 21

bench/rbmap.%.bench: BENCH_PARAMS = 7000000

bench_cross: $(foreach bench,$(CROSS_BENCHES), $(foreach cat, $(CROSS_CATS), bench/$(bench)$(cat).bench))

# yes.
space = $() $()

report_cross.csv: bench_cross report.py
	BENCHES=$(subst $(space),:,$(CROSS_BENCHES)) CATS=$(subst $(space),:,$(CROSS_CATS)) ./report.py > $@

clean:
	-rm *.out bench/*
