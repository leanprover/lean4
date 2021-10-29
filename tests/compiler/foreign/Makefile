CPPFLAGS = -O3
include lean.mk

CPP_SRCS = myfuns.cpp
CPP_OBJS = $(addprefix $(OUT)/testcpp/,$(CPP_SRCS:.cpp=.o))

all: run_test run_testshared run_interp

$(OUT)/testcpp/%.o: %.cpp
	@mkdir -p "$(@D)"
	c++ -std=c++14 -c -o $@ $< $(CPPFLAGS) `leanc --print-cflags`

# to avoid conflicts between the system C++ stdlib needed by the above object file and the internal one used in the Lean runtime,
# we need to dynamically link the foreign code (`test` executable below) or the Lean runtime (`test_leanshared`).

TEST_LINK_FLAGS :=
ifeq ($(OS),Windows_NT)
	SHARED_SUFFIX := dll
else
	TEST_SHARED_LINK_FLAGS := -rpath `lean --print-prefix`/lib/lean
	UNAME := $(shell uname)
	ifeq ($(UNAME),Linux)
		TEST_LINK_FLAGS := -rpath '$$ORIGIN'
		SHARED_SUFFIX := so
	else
		TEST_LINK_FLAGS := -rpath @executable_path
		SHARED_SUFFIX := dylib
	endif
endif

$(BIN_OUT)/testcpp.$(SHARED_SUFFIX): $(CPP_OBJS) | $(BIN_OUT)
	c++ -shared -o $@ $^ `leanc -shared --print-ldflags`

$(BIN_OUT)/test: $(LIB_OUT)/libMain.a $(BIN_OUT)/testcpp.$(SHARED_SUFFIX)
# linking of Lean object files must be done with `leanc`
	leanc -o $@ $^ $(TEST_LINK_FLAGS)

run_test: $(BIN_OUT)/test
	$^

$(BIN_OUT)/test_leanshared: $(LIB_OUT)/libMain.a $(CPP_OBJS) | $(BIN_OUT)
	c++ -o $@ $^ `leanc -shared --print-ldflags` -lleanshared $(TEST_SHARED_LINK_FLAGS)

run_testshared: $(BIN_OUT)/test_leanshared
	$^

# also test interpreter; see doc/dev/ffi.md
$(BIN_OUT)/S.$(SHARED_SUFFIX): $(C_OUT)/Main/S.c $(BIN_OUT)/testcpp.$(SHARED_SUFFIX)
	leanc -shared -o $@ $^ $(TEST_LINK_FLAGS)

run_interp: $(BIN_OUT)/S.$(SHARED_SUFFIX)
	lean --load-dynlib=$^ --run Main.lean
