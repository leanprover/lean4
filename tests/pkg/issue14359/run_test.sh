# Regression test for #14359: a module's comptime initializer must run its runtime initializer,
# because compiled meta code may read globals that only the runtime initializer assigns.
# Loading `Repro.A`'s shared library runs only `meta_initialize_repro_Repro_A`, which used to
# segfault reading a specialization of `describe` that `runtime_initialize_repro_Repro_A` sets.
rm -rf .lake
lake build Repro.A:dynlib Repro.Helper:dynlib
lake env lean ./Repro/B.lean --load-dynlib=$(lake query Repro.A:dynlib) --load-dynlib=$(lake query Repro.Helper:dynlib)
