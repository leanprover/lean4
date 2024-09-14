CXX ?= c++
CPPFLAGS = -O3
# TODO: use Lake instead
include lean.mk

CPP_SRCS = myfuns.cpp
CPP_OBJS = $(addprefix $(OUT)/testcpp/,$(CPP_SRCS:.cpp=.o))

all: run_test run_interp

$(OUT)/testcpp/%.o: %.cpp
	@mkdir -p "$(@D)"
	$(CXX) -std=c++14 -c -o $@ $< $(CPPFLAGS) `leanc --print-cflags`

# to avoid conflicts between the system C++ stdlib needed by the above object file and the internal one used in the Lean runtime,
# we need to dynamically link the Lean runtime.

ifeq ($(OS),Windows_NT)
# make S.so find testcpp.so
  export PATH := $(BIN_OUT):$(PATH)
else
# find libleanshared.so
  TEST_SHARED_LINK_FLAGS := -Wl,-rpath,`lean --print-prefix`/lib/lean
endif

$(BIN_OUT)/testcpp.so: $(CPP_OBJS) | $(BIN_OUT)
	$(CXX) -shared -o $@ $^ `leanc -shared --print-ldflags`

$(BIN_OUT)/test: $(LIB_OUT)/libMain.a $(CPP_OBJS) | $(BIN_OUT)
	$(CXX) -o $@ $^ `leanc -shared --print-ldflags` -lInit_shared -lleanshared_1 -lleanshared $(TEST_SHARED_LINK_FLAGS)

run_test: $(BIN_OUT)/test
	$^

# also test interpreter; see doc/dev/ffi.md
$(BIN_OUT)/S.so: $(C_OUT)/Main/S.c $(BIN_OUT)/testcpp.so
	leanc -shared -o $@ $^

run_interp: $(BIN_OUT)/S.so
	lean --load-dynlib=$^ --run Main.lean
