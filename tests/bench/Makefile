## CONFIG

LEAN_BENCHES = binarytrees binarytrees.st deriv const_fold parser qsort rbmap rbmap_10 rbmap_2 rbmap_1 unionfind
CROSS_BENCHES = binarytrees binarytrees.st deriv const_fold rbmap rbmap_10 rbmap_2 rbmap_1

LEAN_CATS = .lean .no_reuse.lean .no_borrow.lean .no_st.lean
CROSS_CATS = .lean .gc.lean .hs .gc.hs .ml .gc.ml .mlton .gc.mlton .mlkit .gc.mlkit .swift .gc.swift
CROSS_TIME_CATS = .lean .hs .ml .mlton .mlkit .swift
RETIRED_CATS = .gcc.lean .llvm.hs .strict.hs .flambda.ml .lean.perf .hs.perf .ml.perf .mlton.perf .mlkit.perf .swift.perf

LEAN_FLAGS =
LEANC_FLAGS = -O3 -DNDEBUG
GHC_FLAGS = -O3
OCAML_FLAGS = -O3
MLTON_FLAGS =
MLKIT_FLAGS =
SWIFTC_FLAGS = -O -whole-module-optimization

TEMCI_FLAGS = --settings cross.yaml

TEMCI ?= temci
LEAN_BIN ?= ../../bin
GHC ?= ghc
OCAML ?= ocamlopt.opt
MLTON_BIN ?= /usr/bin
MLKIT ?= mlkit
SWIFTC ?= swiftc

PARSER_TEST_FILE ?= ../../src/Init/Prelude.lean

## IMPLEMENTATION

LEAN_INPUTS = $(foreach bench,$(LEAN_BENCHES), $(foreach cat, $(LEAN_CATS), $(bench)$(cat)))
CROSS_INPUTS = $(foreach bench,$(CROSS_BENCHES), $(foreach cat, $(CROSS_CATS), $(bench)$(cat)))

.SECONDARY: $(LEAN_INPUTS:%=%.out) $(LEAN_INPUTS:%=bench/%.bench) $(CROSS_INPUTS:%=%.out) $(CROSS_INPUTS:%=bench/%.bench)
.DELETE_ON_ERROR:

all: report_lean.tex report_cross.tex report

# disable some built-in rules
%.lean:
%.out: %

%.lean.c: %.lean
	$(LEAN_BIN)/lean --c=$@ $(LEAN_FLAGS) $<
%.lean.out: %.lean.c
	$(LEAN_BIN)/leanc $(LEANC_FLAGS) -o $@ $<
# Binaries x.lean.out and x.gcc.lean.out etc. are produced by the
# same rules and x.lean source file by copying the latter to
# x.gcc.lean. This also avoids conflicts between intermediate
# files of the two binaries.
%.gcc.lean.out: LEAN_BIN = $(LEAN_GCC_BIN)
%.gcc.lean: %.lean; ln -f $< $@
%.no_reuse.lean.c: LEAN_BIN = $(LEAN_NO_REUSE_BIN)
%.no_reuse.lean.out: LEAN_BIN = $(LEAN_NO_REUSE_BIN)
%.no_reuse.lean: %.lean; ln -f $< $@
%.no_borrow.lean.c: LEAN_BIN = $(LEAN_NO_BORROW_BIN)
%.no_borrow.lean.out: LEAN_BIN = $(LEAN_NO_BORROW_BIN)
%.no_borrow.lean: %.lean; ln -f $< $@
%.no_st.lean.out: LEAN_BIN = $(LEAN_NO_ST_BIN)
%.no_st.lean: %.lean; ln -f $< $@

%.hs.out: %.hs
	$(GHC) $(GHC_FLAGS) -rtsopts $< -o $@
%.llvm.hs.out: GHC_FLAGS += -fllvm
%.llvm.hs: %.hs; ln -f $< $@
%.strict.hs.out: GHC_FLAGS += -XStrict
%.strict.hs: %.hs; ln -f $< $@

binarytrees.hs: binarytrees.ghc-6.hs; ln -f $< $@
# NOTE: changed `-N4` rtsopt to `-N` to be less system-dependent
binarytrees%hs.out: GHC_FLAGS += --make -O2 -XBangPatterns -dynamic -threaded -rtsopts -with-rtsopts='-N -K128M -H'
binarytrees.st%hs.out: GHC_FLAGS += --make -O2 -XBangPatterns -dynamic -rtsopts -with-rtsopts='-K128M -H'

%.ml.out: %.ml
	$(OCAML) $(OCAML_FLAGS) $< -o $@
%.flambda.ml.out: OCAML = $(OCAML_FLAMBDA)
%.flambda.ml: %.ml; ln -f $< $@

binarytrees.ml: binarytrees5_multicore.ml; ln -f $< $@
binarytrees.st.ml: binarytrees5.ml; ln -f $< $@
binarytrees%ml.out: OCAML_FLAGS += -noassert -fPIC -nodynlink -inline 100 -O3 -package domainslib -linkpkg
binarytrees%ml.out: OCAML = ocamlfind ocamlopt

binarytrees.st.sml: binarytrees.st.mlton-2.sml; ln -f $< $@
%.mlton.out: %.sml
	$(MLTON_BIN)/mlton $(MLTON_FLAGS) -output $@ $<
%.gc.mlton.out: MLTON_FLAGS = -profile time
%.gc.sml: %.sml; ln -f $< $@

%.mlkit.out: %.sml
	$(MLKIT) $(MLKIT_FLAGS) -o $@ $<

%.swift.out: %.swift
	$(SWIFTC) $(SWIFTC_FLAGS) -o $@ $<

binarytrees%swift.out: SWIFTC_FLAGS = -Ounchecked -I Include/swift/apr

bench:
	-@mkdir bench

bench/%.bench: %.out | bench
	ulimit -s unlimited && $(TEMCI) short exec $(TEMCI_FLAGS) -d $< "./$< $(BENCH_PARAMS)" --out $@

bench/parser.%.bench: BENCH_PARAMS = $(PARSER_TEST_FILE) 50

bench/binarytrees.%.bench: BENCH_PARAMS = 21
bench/binarytrees.ml.bench: BENCH_PARAMS = $$(nproc) 21
bench/binarytrees.gc.ml.bench: BENCH_PARAMS = $$(nproc) 21

bench/deriv.%.bench: BENCH_PARAMS = 10

bench/const_fold.%.bench: BENCH_PARAMS = 23

bench/qsort.%.bench: BENCH_PARAMS = 400

bench/rbmap.%.bench: BENCH_PARAMS = 2000000

rbmap_1.%.out: rbmap_checkpoint.%.out; ln -f $< $@
bench/rbmap_1.%.bench: BENCH_PARAMS = 2000000 1

rbmap_2.%.out: rbmap_checkpoint.%.out; ln -f $< $@
bench/rbmap_2.%.bench: BENCH_PARAMS = 2000000 2

rbmap_10.%.out: rbmap_checkpoint.%.out; ln -f $< $@
bench/rbmap_10.%.bench: BENCH_PARAMS = 2000000 10

bench/unionfind.%.bench: BENCH_PARAMS = 3000000

bench/%gc.lean.bench: %lean.out | bench
	ulimit -s unlimited && $(TEMCI) short exec $(TEMCI_FLAGS)\
    -d $< "perf record -o $@.tmp ./$< $(BENCH_PARAMS) >/dev/null && perf report -i $@.tmp -t ';' --stdio -S 'lean_inc_ref_cold,lean_inc_ref_n_cold,lean_dec_ref_cold,lean_del_core,lean_free_small' | ./lean-gc.py"\
	  --runner output --out $@

bench/%gc.hs.bench: %hs.out | bench
	$(TEMCI) short exec $(TEMCI_FLAGS)\
		-d $< "./$< +RTS -t --machine-readable -RTS $(BENCH_PARAMS) 2>&1 >/dev/null | ./ghc-gc.py"\
		--runner output --out $@

bench/%gc.ml.bench: %ml.out | bench
	ulimit -s unlimited && $(TEMCI) short exec $(TEMCI_FLAGS)\
		-d $< "time -ao $@.tmp -f '%U' olly trace $@.tmp './$< $(BENCH_PARAMS)' > /dev/null && ./ocaml-gc.py < $@.tmp"\
		--runner output --out $@

bench/%gc.mlton.bench: %gc.mlton.out | bench
	ulimit -s unlimited && $(TEMCI) short exec $(TEMCI_FLAGS)\
		-d $< './$< $(BENCH_PARAMS) >/dev/null && $(MLTON_BIN)/mlprof ./$< mlmon.out | awk '\''$$1 == "<gc>" { print "gc: " substr($$2, 0, length($$2)-1); found = 1 } END { if (found != 1) { print "gc: 0.000001" } }'\'\
		--runner output --out $@

bench/%gc.mlkit.bench: %gc.mlkit.out | bench
	ulimit -s unlimited && $(TEMCI) short exec $(TEMCI_FLAGS)\
		-d $< "time -f '%e' ./$< -report_gc $(BENCH_PARAMS) 2>&1 >/dev/null | ./mlkit-gc.py"\
		--runner output --out $@

bench/%gc.swift.bench: %swift.out | bench
	ulimit -s unlimited && $(TEMCI) short exec $(TEMCI_FLAGS)\
    -d $< "perf record -o $@.tmp ./$< $(BENCH_PARAMS) >/dev/null && perf report -i $@.tmp -t ';' --stdio | grep -E 'retain|release|dealloc|free' | ./lean-gc.py"\
	  --runner output --out $@

bench/%.perf.bench: %.out | bench
	ulimit -s unlimited && $(TEMCI) short exec $(TEMCI_FLAGS)\
		-d $< "echo > $@.tmp && time -af '%e' perf stat -e cache-misses -x ';' ./$< $(BENCH_PARAMS) 2>&1 >/dev/null | ./perf.py"\
		--runner output --out $@

# no benchmarksgame versions
bench/binarytrees.mlton.bench: ; touch $@
bench/binarytrees.gc.mlton.bench: ; touch $@
bench/binarytrees.mlton.perf.bench: ; touch $@
bench/binarytrees.mlkit.bench: ; touch $@
bench/binarytrees.gc.mlkit.bench: ; touch $@
bench/binarytrees.mlkit.perf.bench: ; touch $@

bench_lean: $(LEAN_INPUTS:%=bench/%.bench)
bench_cross: $(CROSS_INPUTS:%=bench/%.bench)

report/lean: ; -@mkdir -p $@
report/cross: ; -@mkdir -p $@

report/lean/%: $(foreach cat, $(LEAN_CATS), bench/%$(cat).bench) | report/lean
	cat $^ > $@.tmp
	$(TEMCI) report $@.tmp --settings cross.yaml --reporter html2 --html2_out $@ --html2_force_override --properties etime

report/cross/%: $(foreach cat, $(CROSS_TIME_CATS), bench/%$(cat).bench) | report/cross
	cat $^ > $@.tmp
	$(TEMCI) report $@.tmp --settings cross.yaml --reporter html2 --html2_out $@ --html2_force_override --properties etime

report/index.html: $(LEAN_BENCHES:%=report/lean/%) $(CROSS_BENCHES:%=report/cross/%)
	echo "<html><h1>Lean variant benchmarks</h1><ul>"> $@
	for bench in $(LEAN_BENCHES); do \
		echo "<li><a href='lean/$$bench/report.html'>$$bench</a><br><img src='lean/$$bench/fig___SinglesProperty______etime___25.0.svg'></img></li>" >> $@; \
	done
	echo "</ul><h1>Cross-language benchmarks</h1><ul>">> $@
	for bench in $(CROSS_BENCHES); do \
		echo "<li><a href='cross/$$bench/report.html'>$$bench</a><br><img src='cross/$$bench/fig___SinglesProperty______etime___25.0.svg'></img></li>" >> $@; \
	done
	echo "</ul></html>">> $@

report: report/index.html

# yes.
space = $() $()

report_lean.csv report_lean_rbmap.csv: bench_lean
	BENCHES=$(subst $(space),:,$(LEAN_BENCHES)) CATS=$(subst $(space),:,$(LEAN_CATS)) ./report.py report_lean
	column -s';' -t < $@

report_cross.csv report_cross_rbmap.csv: bench_cross
	BENCHES=$(subst $(space),:,$(CROSS_BENCHES)) CATS=$(subst $(space),:,$(CROSS_CATS)) ./report.py report_cross
	column -s';' -t < $@

TO_TEX = 's/-/---/g;s/%/\\%/g;s/\.$$//g;s/(\([0-9]\)\([0-9]\))/\\ensuremath{\\tilde{\1}\\tilde{\2}}/g;s/(\([0-9]\))/\\ensuremath{\\tilde{\1}}/g;s/;/ \& /g;s/$$/\\\\/'
report_%.tex: report_%.csv
	tail -n +2 $< | head -n -1 | sed 's/^\([^;]\+\)/\\verb!\1!/;'$(TO_TEX) > $@
	echo -n '\midrule ' >> $@
	tail -n 1 $< | sed 's/. /.\\ /;'$(TO_TEX) >> $@

clean:
	-rm *.out bench/*
