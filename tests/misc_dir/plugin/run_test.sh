# LEAN_EXPORTING needs to be defined for .c files included in shared libraries
lean --c=SnakeLinter.c -Dcompiler.postponeCompile=false SnakeLinter.lean
leanc ${LEANC_OPTS-} -O3 -DNDEBUG -DLEAN_EXPORTING -shared -o SnakeLinter.so SnakeLinter.c

capture_only SnakeLinter.lean \
  lean -Dlinter.all=false --plugin=SnakeLinter.so SnakeLinter.lean
check_out_file
check_exit_is_fail
