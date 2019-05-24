## CONFIG

CROSS_BENCHES = binarytrees deriv expr_const_folding qsort rbmap rbmap_checkpoint_10 rbmap_shared

CROSS_CATS = .lean .gc.lean .lean.perf .gcc.lean .hs .gc.hs .hs.perf .llvm.hs .ml .gc.ml .ml.perf .mlton .mlton.perf .mlkit .mlkit.perf
TIME_CATS = .lean .hs .llvm.hs .ml .mlton .mlkit
RETIRED_CATS = .gcc.lean .flambda.ml

LEANC_FLAGS = -O3
GHC_FLAGS = -O3
OCAML_FLAGS = -O3
MLTON_FLAGS =
MLKIT_FLAGS =

TEMCI ?= temci
LEAN_BIN ?= ../../bin
GHC ?= ghc
OCAML ?= ocamlopt.opt
MLTON ?= mlton
MLKIT ?= mlkit

## IMPLEMENTATION

CROSS_INPUTS = $(foreach bench,$(CROSS_BENCHES), $(foreach cat, $(CROSS_CATS), $(bench)$(cat)))

.SECONDARY: $(CROSS_INPUTS:%=%.out) $(CROSS_INPUTS:%=bench/%.bench)
.DELETE_ON_ERROR:

all: reports report_cross.csv

# disable some built-in rules
%.lean:
%.out: %

%.lean.cpp: %.lean
	$(LEAN_BIN)/lean --cpp=$@ $<
%.lean.out: %.lean.cpp
	$(LEAN_BIN)/leanc $(LEANC_FLAGS) -o $@ $<
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

%.mlton.out: %.sml
	$(MLTON) $(MLTON_FLAGS) -output $@ $<

%.mlkit.out: %.sml
	$(MLKIT) $(MLKIT_FLAGS) -o $@ $<

bench:
	-@mkdir bench

bench/%.bench: %.out | bench
	ulimit -s unlimited && $(TEMCI) short exec -d $< "./$< $(BENCH_PARAMS)" --out $@

bench/binarytrees.%.bench: BENCH_PARAMS = 21

bench/qsort.%.bench: BENCH_PARAMS = 250

bench/rbmap.%.bench: BENCH_PARAMS = 7000000

rbmap_shared.%.out: rbmap_checkpoint.%.out; ln -f $< $@
bench/rbmap_shared.%.bench: BENCH_PARAMS = 500000 1

rbmap_checkpoint_10.%.out: rbmap_checkpoint.%.out; ln -f $< $@
bench/rbmap_checkpoint_10.%.bench: BENCH_PARAMS = 2000000 10

bench/%gc.lean.bench: %lean.out | bench
	ulimit -s unlimited && $(TEMCI) short exec\
    -d $< "perf record -o $@.tmp ./$< $(BENCH_PARAMS) >/dev/null && perf report -i $@.tmp -t ';' --stdio -S 'lean::del,lean::dealloc' | ./lean-gc.py"\
	  --runner output --out $@

bench/%gc.hs.bench: %hs.out | bench
	$(TEMCI) short exec\
		-d $< "./$< +RTS -t --machine-readable -RTS $(BENCH_PARAMS) 2>&1 >/dev/null | ./ghc-gc.py"\
		--runner output --out $@

bench/%gc.ml.bench: %gc.ml.out | bench
	ulimit -s unlimited && $(TEMCI) short exec\
		-d $< "echo > $@.tmp && OCAML_INSTR_FILE=$@.tmp time -ao $@.tmp -f '%e' ./$< $(BENCH_PARAMS) >/dev/null && ./ocaml-gc.py < $@.tmp"\
		--runner output --out $@

bench/%.perf.bench: %.out | bench
	ulimit -s unlimited && $(TEMCI) short exec\
		-d $< "echo > $@.tmp && time -af '%e' perf stat -e cache-misses -x ';' ./$< $(BENCH_PARAMS) 2>&1 >/dev/null | ./perf.py"\
		--runner output --out $@

# fork() breaks instrumentation
bench/binarytrees.gc.ml.bench: ; touch $@

# no benchmarksgame versions
bench/binarytrees%mlton.bench: ; touch $@
bench/binarytrees%mlton.perf.bench: ; touch $@
bench/binarytrees%mlkit.bench: ; touch $@
bench/binarytrees%mlkit.perf.bench: ; touch $@

bench_cross: $(CROSS_INPUTS:%=bench/%.bench)

report:
	-@mkdir report

report/%: $(foreach cat, $(TIME_CATS), bench/%$(cat).bench) | report
	cat $^ > $@.tmp
	$(TEMCI) report $@.tmp --settings_file temci.yaml --reporter html2 --html2_out $@ --html2_force_override --properties etime

report/index.html: | report
	echo > $@
	for bench in $(CROSS_BENCHES); do \
		echo "<a href='$$bench/report.html'>$$bench</a>" >> $@; \
	done

reports: $(foreach bench, $(CROSS_BENCHES), report/$(bench)) report/index.html

# yes.
space = $() $()

report_cross.csv: bench_cross report.py
	BENCHES=$(subst $(space),:,$(CROSS_BENCHES)) CATS=$(subst $(space),:,$(CROSS_CATS)) ./report.py > $@

clean:
	-rm *.out bench/*
