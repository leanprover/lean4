LAKE ?= lake
LEANC ?= leanc

.PHONY: all run run-local lake assert-fat

all: run run-local

# Link C binary against Lake package dynamic library

lake:
	$(LAKE) --dir=lib/rffi build

OUT_DIR = out
LEAN_SYSROOT ?= $(shell lean --print-prefix)
LEAN_LIBDIR := $(LEAN_SYSROOT)/lib/lean

$(OUT_DIR):
	mkdir -p $@

ifneq ($(OS),Windows_NT)
# Add shared library paths to loader path (no Windows equivalent)
LINK_FLAGS=-Wl,-rpath,$(LEAN_LIBDIR) -Wl,-rpath,$(PWD)/lib/.lake/build/lib
endif

ifeq ($(OS),Windows_NT)
STATICLIB_NAME := RFFIFat.a
else
STATICLIB_NAME := libRFFIFat.a
endif

$(OUT_DIR)/main: main.c lake | $(OUT_DIR)
# Add library paths for Lake package and for Lean itself
	cc -o $@ $< -I $(LEAN_SYSROOT)/include -L $(LEAN_LIBDIR) lib/rffi/.lake/build/lib/$(STATICLIB_NAME) -lInit_shared -lleanshared $(LINK_FLAGS)

run: $(OUT_DIR)/main
ifeq ($(OS),Windows_NT)
# Add shared library paths to loader path dynamically
	env PATH="lib/.lake/build/lib:$(shell cygpath $(LEAN_SYSROOT))/bin:$(PATH)" $(OUT_DIR)/main
else
	$(OUT_DIR)/main
endif

# Alternatively, we can copy all shared lib dependencies to the current directory
# in order to avoid path set up and obtain a more portable executable

ifeq ($(OS),Windows_NT)
SHLIB_PREFIX :=
SHLIB_EXT := dll
LEAN_SHLIB_ROOT := $(shell cygpath $(LEAN_SYSROOT)/bin)
else
SHLIB_PREFIX := lib
# Add current directory to loader path (default on Windows)
ifeq ($(shell uname -s),Darwin)
LINK_FLAGS_LOCAL := -Wl,-rpath,@executable_path
SHLIB_EXT := a
else
LINK_FLAGS_LOCAL := -Wl,-rpath,'$${ORIGIN}'
SHLIB_EXT := so
endif
LEAN_SHLIB_ROOT := $(LEAN_LIBDIR)
endif

$(OUT_DIR)/main-local: main.c lake | $(OUT_DIR)
	cp -f $(LEAN_SHLIB_ROOT)/*.$(SHLIB_EXT) $(OUT_DIR)
	cc -o $@ $< -I $(LEAN_SYSROOT)/include -L $(OUT_DIR) lib/rffi/.lake/build/lib/$(STATICLIB_NAME) -lInit_shared -lleanshared $(LINK_FLAGS_LOCAL)

# Assert that we have the 'initialize' for the 'other_lean_lib' dependency
assert-fat:
	strings lib/rffi/.lake/build/lib/$(STATICLIB_NAME) | grep "_initialize_Dep_Basic"

run-local: $(OUT_DIR)/main-local
	$(OUT_DIR)/main-local
