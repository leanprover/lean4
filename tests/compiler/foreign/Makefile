PKG = main
CPPFLAGS = -O3
include lean.mk

CPP_SRCS = myfuns.cpp
CPP_OBJS = $(addprefix $(OUT)/testcpp/,$(CPP_SRCS:.cpp=.o))

all: $(BIN_OUT)/test

$(OUT)/testcpp/%.o: %.cpp
	@mkdir -p "$(@D)"
	c++ -std=c++14 -c -o $@ $< $(CPPFLAGS) `leanc --print-cflags`

$(BIN_OUT)/test: $(LIB_OUT)/libmain.a $(CPP_OBJS) | $(BIN_OUT)
	c++ -o $@ $^ `leanc --print-ldflags`
