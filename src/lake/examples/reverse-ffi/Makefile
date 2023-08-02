.PHONY: all run run-local lake

all: run run-local

# Link C binary against Lake package dynamic library

lake:
	lake --dir=lib build

ifneq ($(OS),Windows_NT)
# Add shared library paths to loader path (no Windows equivalent)
  LINK_FLAGS=-Wl,-rpath,`lean --print-prefix`/lib/lean -Wl,-rpath,$(PWD)/lib/build/lib
endif

main: main.c lake
# Add library paths for Lake package and for Lean itself
	cc -o $@ $< -I `lean --print-prefix`/include -L `lean --print-libdir` -L lib/build/lib -lRFFI -lleanshared $(LINK_FLAGS)

run: main
ifeq ($(OS),Windows_NT)
# Add shared library path to loader path dynamically (`lean`'s directory is already in `PATH`)
	PATH=lib/build/lib:$(PATH) ./main
else
	./main
endif

# Alternatively, we can copy all shared lib dependencies to the current directory
# in order to avoid path set up and obtain a more portable executable

ifeq ($(OS),Windows_NT)
  SHLIB_EXT=dll
else
  # Add current directory to loader path (default on Windows)
  ifeq ($(shell uname -s),Darwin)
    LINK_FLAGS_LOCAL=-Wl,-rpath,@executable_path
    SHLIB_EXT=dylib
  else
    LINK_FLAGS_LOCAL=-Wl,-rpath,$$ORIGIN
    SHLIB_EXT=so
  endif
endif

main-local: main.c lake
	cp -f `lean --print-libdir`/libleanshared.$(SHLIB_EXT) lib/build/lib/libRFFI.$(SHLIB_EXT) .
	cc -o $@ $< -I `lean --print-prefix`/include -L . -lRFFI -lleanshared $(LINK_FLAGS_LOCAL)

run-local: main-local
	./main-local
